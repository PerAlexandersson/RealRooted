module

public import RealRooted.Mesh.HermitePoulain

/-!
# The discrete Hermite--Poulain theorem, necessity

Brändén, Krasikov, and Shapiro, *Elements of Pólya--Schur theory in the finite difference
setting*, Proc. AMS 144 (2016), Theorem 3: the operator `p ↦ a₀ p(x) + a₁ p(x - 1) + ⋯ +
a_k p(x - k)` maps polynomials of mesh at least one to polynomials of mesh at least one if and
only if all zeros of its symbol `a₀ + a₁ t + ⋯ + a_k t^k` are real and nonnegative.  The
sufficiency direction is `RealRooted.finiteDifferenceOp_meshGE`; this module proves the
necessity direction and the resulting equivalence.

The necessity proof was found and formalized by Aristotle (Harmonic) and ported here.  We apply
the operator to the falling factorials `x (x - 1) ⋯ (x - i + 1)`.  The cofactors of the factors
`x - k, …, x - i + 1` are real-rooted, with roots away from the interval `[k, i - 1]`.  After
rescaling `x ↦ i x` and letting `i → ∞`, they converge to the polynomial `x^k Q((x - 1)/x)`,
whose roots are therefore `x` with `x = 1 / (1 - t)` for the roots `t` of `Q`; real-rootedness
and nonnegativity of the `t` follow.  See RealRooted issue #2070.
-/

public section

open Polynomial

namespace RealRooted

noncomputable section

/-- The hypothesis of the necessity direction: `finiteDifferenceOp 1 Q` preserves mesh at least
one. -/
private abbrev PreservesMeshOne (Q : ℝ[X]) : Prop :=
  ∀ p : ℝ[X], p.MeshGE 1 → (finiteDifferenceOp 1 Q p).MeshGE 1

/-- The falling factorial `X (X - 1) ⋯ (X - i + 1)`. -/
private def fallPoly (i : ℕ) : ℝ[X] := ∏ m ∈ Finset.range i, (X - C (m : ℝ))

/-- The cofactor `R_i` with
`finiteDifferenceOp 1 Q (fallPoly i) = (X - k) ⋯ (X - i + 1) * R_i`. -/
private def cofPoly (Q : ℝ[X]) (i : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (Q.natDegree + 1), C (Q.coeff j) *
    ((∏ m ∈ Finset.Ico j Q.natDegree, (X - C (m : ℝ))) *
      ∏ l ∈ Finset.range j, (X - C ((i : ℝ) + l)))

/-- The rescaled cofactor, as a function of `ε = 1/i`. -/
private def scalCof (Q : ℝ[X]) (ε : ℝ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (Q.natDegree + 1), (Q.coeff j : ℂ) *
    ((∏ m ∈ Finset.Ico j Q.natDegree, (z - (m : ℂ) * ε)) *
      ∏ l ∈ Finset.range j, (z - 1 - (l : ℂ) * ε))

/-- The limit polynomial `x^k Q((x - 1)/x)`. -/
private def limitPoly (Q : ℝ[X]) : ℂ[X] :=
  ∑ j ∈ Finset.range (Q.natDegree + 1),
    C (Q.coeff j : ℂ) * (X ^ (Q.natDegree - j) * (X - 1) ^ j)

private lemma finiteDifferenceOp_fallPoly (Q : ℝ[X]) (i : ℕ) (hi : Q.natDegree ≤ i) :
    finiteDifferenceOp 1 Q (fallPoly i) =
      (∏ m ∈ Finset.Ico Q.natDegree i, (X - C (m : ℝ))) * cofPoly Q i := by
  unfold finiteDifferenceOp
  rw [sum_over_range _ (fun n => by simp), cofPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [mul_one]
  have hjk : j ≤ Q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have e0 : (fallPoly i).comp (X - C (j : ℝ)) =
      ∏ n ∈ Finset.Ico j (j + i), (X - C (n : ℝ)) := by
    rw [fallPoly, prod_comp, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]
    refine Finset.prod_congr rfl fun m _ => ?_
    simp only [sub_comp, X_comp, C_comp]
    push_cast; rw [C_add]; ring
  have e1 : ∏ n ∈ Finset.Ico i (j + i), (X - C (n : ℝ)) =
      ∏ l ∈ Finset.range j, (X - C ((i : ℝ) + l)) := by
    rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun m _ => ?_
    push_cast; rfl
  rw [e0, ← Finset.prod_Ico_consecutive _ hjk (by lia : Q.natDegree ≤ j + i),
    ← Finset.prod_Ico_consecutive _ hi (by lia : i ≤ j + i), e1]
  ring

private lemma meshGE_fallPoly (i : ℕ) : (fallPoly i).MeshGE 1 := by
  have hf : fallPoly i = (Multiset.map (fun a => X - C a)
      (((List.range i).map (fun m : ℕ => (m : ℝ)) : List ℝ) : Multiset ℝ)).prod := by
    rw [fallPoly, Finset.prod_eq_multiset_prod, Multiset.map_coe, List.map_map]
    rfl
  have hroots : (fallPoly i).roots =
      (((List.range i).map (fun m : ℕ => (m : ℝ)) : List ℝ) : Multiset ℝ) := by
    rw [hf, roots_multiset_prod_X_sub_C]
  have hsort : (fallPoly i).roots.sort (· ≤ ·) =
      (List.range i).map (fun m : ℕ => (m : ℝ)) := by
    rw [hroots, Multiset.coe_sort, List.mergeSort_eq_self]
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range).imp fun h => by exact_mod_cast h.le
  have hdeg : (fallPoly i).natDegree = i := by
    rw [fallPoly, natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range]
  refine ⟨splits_iff_card_roots.2 (by rw [hroots, hdeg]; simp), zero_le_one, ?_⟩
  rw [hsort]
  intro n hn
  simp only [List.length_map, List.length_range] at hn
  rw [List.getD_eq_getElem _ _ (by simp; lia), List.getD_eq_getElem _ _ (by simp; lia)]
  simp

private lemma mesh_pair (f : ℝ[X]) (hf : f.MeshGE 1) (r s : ℝ)
    (h : ({r, s} : Multiset ℝ) ≤ f.roots) :
    1 ≤ |r - s| := by
  obtain ⟨-, -, h3⟩ := hf
  set l := f.roots.sort (· ≤ ·) with hl
  have hP : l.Pairwise (fun x y => x + 1 ≤ y) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    induction j, hij using Nat.le_induction with
    | base =>
      have := h3 i hj
      rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at this
    | succ j hij ih =>
      have h1 := ih (by lia)
      have h2 := h3 j hj
      rw [List.getD_eq_getElem _ _ (by lia), List.getD_eq_getElem _ _ hj] at h2
      linarith
  have hP' : l.Pairwise (fun x y => 1 ≤ |x - y|) := hP.imp fun {x y} hxy => by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  have hl' : (l : Multiset ℝ) = f.roots := Multiset.sort_eq _ _
  have hrs : ({r, s} : Multiset ℝ) = ((([r, s] : List ℝ)) : Multiset ℝ) := rfl
  rw [← hl', hrs, Multiset.coe_le] at h
  obtain ⟨l', hperm, hsub⟩ := h
  have := (hP'.sublist hsub).perm hperm (fun hxy => by rwa [abs_sub_comm])
  simpa using this

private lemma natDegree_cofPoly_le (Q : ℝ[X]) (i : ℕ) :
    (cofPoly Q i).natDegree ≤ Q.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjk : j ≤ Q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
  rw [natDegree_finsetProd_X_sub_C_eq_card, natDegree_finsetProd_X_sub_C_eq_card,
    Nat.card_Ico, Finset.card_range]
  lia

private lemma cofPoly_realRooted (Q : ℝ[X]) (hT : PreservesMeshOne Q)
    (i : ℕ) (hi : Q.natDegree ≤ i) : (cofPoly Q i).Splits := by
  by_cases hR : cofPoly Q i = 0
  · simp [hR]
  have hP : (∏ m ∈ Finset.Ico Q.natDegree i, (X - C (m : ℝ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m _ => X_sub_C_ne_zero _
  have hmesh := (hT _ (meshGE_fallPoly i)).1
  rw [finiteDifferenceOp_fallPoly Q i hi] at hmesh
  exact hmesh.of_dvd (mul_ne_zero hP hR) (dvd_mul_left _ _)

private lemma cofPoly_roots_loc (Q : ℝ[X]) (hT : PreservesMeshOne Q)
    (i : ℕ) (hi : Q.natDegree ≤ i) (r : ℝ) (hr : r ∈ (cofPoly Q i).roots) :
    r < Q.natDegree ∨ (i : ℝ) - 1 < r := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hkr, hri⟩ := hcon
  have hR : cofPoly Q i ≠ 0 := ne_zero_of_mem_roots hr
  have hP : (∏ m ∈ Finset.Ico Q.natDegree i, (X - C (m : ℝ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m _ => X_sub_C_ne_zero _
  have hr0 : 0 ≤ r := le_trans (Nat.cast_nonneg _) hkr
  set j := ⌊r⌋₊ with hj
  have hj1 : (j : ℝ) ≤ r := Nat.floor_le hr0
  have hj2 : r < j + 1 := Nat.lt_floor_add_one r
  have hkj : Q.natDegree ≤ j := Nat.le_floor hkr
  have hji : j < i := by
    have : (j : ℝ) < i := by linarith
    exact_mod_cast this
  have hdvd : (X - C r) * (X - C (j : ℝ)) ∣ finiteDifferenceOp 1 Q (fallPoly i) := by
    rw [finiteDifferenceOp_fallPoly Q i hi, mul_comm (∏ m ∈ Finset.Ico Q.natDegree i, _)]
    apply mul_dvd_mul
    · exact dvd_iff_isRoot.2 ((mem_roots hR).1 hr)
    · exact Finset.dvd_prod_of_mem (fun m : ℕ => X - C (m : ℝ))
        (Finset.mem_Ico.2 ⟨hkj, hji⟩)
  have hne : finiteDifferenceOp 1 Q (fallPoly i) ≠ 0 := by
    rw [finiteDifferenceOp_fallPoly Q i hi]
    exact mul_ne_zero hP hR
  have hle := roots.le_of_dvd hne hdvd
  rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
    roots_X_sub_C] at hle
  have := mesh_pair _ (hT _ (meshGE_fallPoly i)) r j hle
  rw [abs_of_nonneg (by linarith)] at this
  linarith

private lemma normSq_aeval_le (g : ℝ[X]) (hg : g.roots.card = g.natDegree) (k : ℕ)
    (hk : g.natDegree ≤ k) (z w : ℂ) (M : ℝ) (hM : 1 ≤ M)
    (h : ∀ r ∈ g.roots, (z.re - r) ^ 2 + z.im ^ 2 ≤ M * ((w.re - r) ^ 2 + w.im ^ 2)) :
    Complex.normSq (aeval z g) ≤ M ^ k * Complex.normSq (aeval w g) := by
  have hev : ∀ u : ℂ, Complex.normSq (aeval u g) = Complex.normSq (g.leadingCoeff : ℂ) *
      (g.roots.map fun r => (u.re - r) ^ 2 + u.im ^ 2).prod := by
    intro u
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hg]
    rw [map_mul, aeval_C, map_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod,
      Multiset.map_map, Complex.coe_algebraMap]
    congr 2
    apply Multiset.map_congr rfl
    intro r _
    simp [Complex.normSq_apply]; ring
  rw [hev z, hev w]
  have hM0 : 0 ≤ M := by linarith
  have key : ∀ s : Multiset ℝ, (∀ r ∈ s, (z.re - r) ^ 2 + z.im ^ 2 ≤
      M * ((w.re - r) ^ 2 + w.im ^ 2)) →
      (s.map fun r => (z.re - r) ^ 2 + z.im ^ 2).prod ≤
        M ^ Multiset.card s * (s.map fun r => (w.re - r) ^ 2 + w.im ^ 2).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      intro hs
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
      have h1 := hs a (Multiset.mem_cons_self _ _)
      have h2 := ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)
      have h3 : 0 ≤ (s.map fun r => (z.re - r) ^ 2 + z.im ^ 2).prod :=
        Multiset.prod_nonneg fun x hx => by
          obtain ⟨r, _, rfl⟩ := Multiset.mem_map.1 hx; positivity
      have h4 : 0 ≤ (z.re - a) ^ 2 + z.im ^ 2 := by positivity
      calc ((z.re - a) ^ 2 + z.im ^ 2) * (s.map fun r => (z.re - r) ^ 2 + z.im ^ 2).prod
          ≤ (M * ((w.re - a) ^ 2 + w.im ^ 2)) *
              (M ^ Multiset.card s * (s.map fun r => (w.re - r) ^ 2 + w.im ^ 2).prod) :=
            mul_le_mul h1 h2 h3 (by linarith)
        _ = _ := by ring_nf
  have hk' := key g.roots h
  have hP : 0 ≤ (g.roots.map fun r => (w.re - r) ^ 2 + w.im ^ 2).prod :=
    Multiset.prod_nonneg fun x hx => by
      obtain ⟨r, _, rfl⟩ := Multiset.mem_map.1 hx; positivity
  have hpow : M ^ Multiset.card g.roots ≤ M ^ k := by
    rw [hg]; exact pow_le_pow_right₀ hM hk
  have hL : 0 ≤ Complex.normSq (g.leadingCoeff : ℂ) := Complex.normSq_nonneg _
  calc Complex.normSq (g.leadingCoeff : ℂ) *
        (g.roots.map fun r => (z.re - r) ^ 2 + z.im ^ 2).prod
      ≤ Complex.normSq (g.leadingCoeff : ℂ) *
        (M ^ k * (g.roots.map fun r => (w.re - r) ^ 2 + w.im ^ 2).prod) := by
        apply mul_le_mul_of_nonneg_left _ hL
        exact hk'.trans (mul_le_mul_of_nonneg_right hpow hP)
    _ = _ := by ring

private lemma aeval_cofPoly (Q : ℝ[X]) (i : ℕ) (hi : 0 < i) (z : ℂ) :
    aeval ((i : ℂ) * z) (cofPoly Q i) =
      (i : ℂ) ^ Q.natDegree * scalCof Q (1 / (i : ℝ)) z := by
  have hi0 : (i : ℂ) ≠ 0 := by exact_mod_cast hi.ne'
  rw [cofPoly, scalCof, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ Q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  simp only [map_mul, aeval_C, map_prod, map_sub, aeval_X, Complex.coe_algebraMap]
  have e1 : ∏ m ∈ Finset.Ico j Q.natDegree, ((i : ℂ) * z - ((m : ℝ) : ℂ)) =
      (i : ℂ) ^ (Q.natDegree - j) *
        ∏ m ∈ Finset.Ico j Q.natDegree, (z - (m : ℂ) * ((1 / (i : ℝ) : ℝ) : ℂ)) := by
    rw [← Nat.card_Ico j Q.natDegree, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun m _ => ?_
    push_cast; field_simp
  have e2 : ∏ l ∈ Finset.range j, ((i : ℂ) * z - (((i : ℝ) + l : ℝ) : ℂ)) =
      (i : ℂ) ^ j *
        ∏ l ∈ Finset.range j, (z - 1 - (l : ℂ) * ((1 / (i : ℝ) : ℝ) : ℂ)) := by
    rw [show (i : ℂ) ^ j = ∏ _l ∈ Finset.range j, (i : ℂ) by simp,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun m _ => ?_
    push_cast; field_simp; ring
  rw [e1, e2]
  have : (i : ℂ) ^ Q.natDegree = (i : ℂ) ^ (Q.natDegree - j) * (i : ℂ) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hjk]
  rw [this]; ring

private lemma tendsto_scalCof (Q : ℝ[X]) (z : ℂ) :
    Filter.Tendsto (fun i : ℕ => scalCof Q (1 / (i : ℝ)) z) Filter.atTop
      (nhds (scalCof Q 0 z)) := by
  have hc : Continuous fun ε : ℝ => scalCof Q ε z := by
    unfold scalCof; fun_prop
  exact (hc.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat

private lemma eval_limitPoly (Q : ℝ[X]) (z : ℂ) : (limitPoly Q).eval z = scalCof Q 0 z := by
  simp [scalCof, limitPoly, eval_finsetSum, Finset.prod_const, Nat.card_Ico]

private lemma limitPoly_ne_zero (Q : ℝ[X]) (hQ : Q ≠ 0) : limitPoly Q ≠ 0 := by
  intro h0
  have h := congrArg (eval 0) h0
  rw [eval_zero, limitPoly, eval_finsetSum, Finset.sum_eq_single Q.natDegree] at h
  · have h' : ((Q.coeff Q.natDegree : ℝ) : ℂ) * (-1) ^ Q.natDegree = 0 := by simpa using h
    have h'' : Q.coeff Q.natDegree = 0 := by simpa using h'
    exact hQ (leadingCoeff_eq_zero.1 h'')
  · intro j hj hjk
    have : 0 < Q.natDegree - j := by
      have := Finset.mem_range.1 hj; lia
    simp [zero_pow this.ne']
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h

private lemma limitPoly_no_bad_root (Q : ℝ[X]) (hQ : Q ≠ 0)
    (hT : PreservesMeshOne Q) (a c : ℝ)
    (hac : c ≠ 0 ∨ (c = 0 ∧ 0 < a ∧ a < 1)) :
    (limitPoly Q).eval ((a : ℂ) + (c : ℂ) * Complex.I) ≠ 0 := by
  intro hroot
  set k := Q.natDegree with hk
  -- uniform separation of the roots of `cofPoly Q i` from `i * (a + c I)`
  obtain ⟨δ, hδ, N, hN⟩ : ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      0 < i ∧ k ≤ i ∧ ∀ r ∈ (cofPoly Q i).roots,
        ((i : ℝ) * δ) ^ 2 ≤ ((i : ℝ) * a - r) ^ 2 + ((i : ℝ) * c) ^ 2 := by
    rcases hac with hc | ⟨hc, ha0, ha1⟩
    · refine ⟨|c|, abs_pos.2 hc, k + 1, fun i hi => ⟨by lia, by lia, fun r _ => ?_⟩⟩
      have : ((i : ℝ) * |c|) ^ 2 = ((i : ℝ) * c) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
      rw [this]; nlinarith [sq_nonneg ((i : ℝ) * a - r)]
    · obtain ⟨N, hN⟩ := exists_nat_gt (2 * k / a + 2 / (1 - a) + k + 1)
      refine ⟨min a (1 - a) / 2, by positivity, N, fun i hi => ?_⟩
      have hiN : (N : ℝ) ≤ i := by exact_mod_cast hi
      have h1 : 0 ≤ 2 * k / a := by positivity
      have h2 : 0 < 2 / (1 - a) := by apply div_pos <;> linarith
      have hik : (k : ℝ) < i := by linarith
      refine ⟨by exact_mod_cast (show (0 : ℝ) < i by linarith), by exact_mod_cast hik.le,
        fun r hr => ?_⟩
      have hia : 2 * k < (i : ℝ) * a := by
        have : 2 * k / a < i := by linarith
        rwa [div_lt_iff₀ ha0] at this
      have hia' : 2 < (i : ℝ) * (1 - a) := by
        have : 2 / (1 - a) < i := by linarith
        rwa [div_lt_iff₀ (by linarith)] at this
      have hipos : (0 : ℝ) ≤ i := by linarith
      have hm1 : min a (1 - a) ≤ a := min_le_left _ _
      have hm2 : min a (1 - a) ≤ 1 - a := min_le_right _ _
      have hsep : (i : ℝ) * (min a (1 - a) / 2) ≤ |(i : ℝ) * a - r| := by
        rcases cofPoly_roots_loc Q hT i (by exact_mod_cast hik.le) r hr with hr' | hr'
        · rw [abs_of_nonneg (by nlinarith)]
          nlinarith
        · rw [abs_of_nonpos (by nlinarith)]
          nlinarith
      rw [hc, mul_zero, sq (0 : ℝ), mul_zero, add_zero, ← sq_abs ((i : ℝ) * a - r)]
      exact pow_le_pow_left₀ (by positivity) hsep 2
  -- the limit function vanishes on the whole vertical line through `a`
  have hline : ∀ b : ℝ, (limitPoly Q).eval ((a : ℂ) + (b : ℂ) * Complex.I) = 0 := by
    intro b
    set M : ℝ := 1 + b ^ 2 / δ ^ 2 with hM
    have hM1 : 1 ≤ M := by have : 0 ≤ b ^ 2 / δ ^ 2 := by positivity
                           linarith
    have hineq : ∀ i : ℕ, N ≤ i →
        Complex.normSq (scalCof Q (1 / (i : ℝ)) ((a : ℂ) + (b : ℂ) * Complex.I)) ≤
          M ^ k *
            Complex.normSq (scalCof Q (1 / (i : ℝ)) ((a : ℂ) + (c : ℂ) * Complex.I)) := by
      intro i hi
      obtain ⟨hi0, hki, hroots⟩ := hN i hi
      have hcard := splits_iff_card_roots.1 (cofPoly_realRooted Q hT i hki)
      have hmain := normSq_aeval_le (cofPoly Q i) hcard k
        (natDegree_cofPoly_le Q i) ((i : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I))
        ((i : ℂ) * ((a : ℂ) + (c : ℂ) * Complex.I)) M hM1 (by
          intro r hr
          have hD := hroots r hr
          simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
            Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
          ring_nf
          ring_nf at hD
          have hδ2 : 0 < δ ^ 2 := by positivity
          have hkey : (i : ℝ) ^ 2 * b ^ 2 ≤ b ^ 2 / δ ^ 2 *
              ((i : ℝ) ^ 2 * a ^ 2 - (i : ℝ) * a * r * 2 + (i : ℝ) ^ 2 * c ^ 2 + r ^ 2) := by
            have : b ^ 2 / δ ^ 2 * ((i : ℝ) ^ 2 * δ ^ 2) = (i : ℝ) ^ 2 * b ^ 2 := by
              field_simp
            rw [← this]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
          rw [hM]
          nlinarith)
      rw [aeval_cofPoly Q i hi0, aeval_cofPoly Q i hi0, map_mul, map_mul, map_pow] at hmain
      have hpos : 0 < Complex.normSq (i : ℂ) ^ k := by
        apply pow_pos; rw [Complex.normSq_pos]; exact_mod_cast hi0.ne'
      have := hmain
      rw [show M ^ k * (Complex.normSq (i : ℂ) ^ k *
          Complex.normSq (scalCof Q (1 / (i : ℝ)) ((a : ℂ) + (c : ℂ) * Complex.I))) =
          Complex.normSq (i : ℂ) ^ k * (M ^ k *
          Complex.normSq (scalCof Q (1 / (i : ℝ)) ((a : ℂ) + (c : ℂ) * Complex.I))) by ring]
        at this
      exact le_of_mul_le_mul_left this hpos
    have hlim := le_of_tendsto_of_tendsto
      ((Complex.continuous_normSq.tendsto _).comp
        (tendsto_scalCof Q ((a : ℂ) + (b : ℂ) * Complex.I)))
      (((Complex.continuous_normSq.tendsto _).comp
        (tendsto_scalCof Q ((a : ℂ) + (c : ℂ) * Complex.I))).const_mul (M ^ k))
      (Filter.eventually_atTop.2 ⟨N, hineq⟩)
    rw [← eval_limitPoly, ← eval_limitPoly, hroot, map_zero, mul_zero] at hlim
    exact Complex.normSq_eq_zero.1 (le_antisymm hlim (Complex.normSq_nonneg _))
  apply limitPoly_ne_zero Q hQ
  apply eq_zero_of_infinite_isRoot
  have hinj : Function.Injective fun b : ℝ => (a : ℂ) + (b : ℂ) * Complex.I := by
    intro b1 b2 h
    have := congrArg Complex.im h
    simpa using this
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
  rintro _ ⟨b, rfl⟩
  exact hline b

private lemma eval_limitPoly_inv (Q : ℝ[X]) (t : ℂ) (ht : t ≠ 1) :
    (limitPoly Q).eval (1 / (1 - t)) = (1 / (1 - t)) ^ Q.natDegree * aeval t Q := by
  have h1t : (1 - t) ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  set x : ℂ := 1 / (1 - t) with hx
  have hx1 : x - 1 = x * t := by rw [hx]; field_simp; ring
  rw [limitPoly, eval_finsetSum, aeval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ Q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one, hx1, mul_pow]
  rw [Algebra.smul_def, Complex.coe_algebraMap]
  have : x ^ Q.natDegree = x ^ (Q.natDegree - j) * x ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hjk]
  rw [this]; ring

private lemma complex_root_good (Q : ℝ[X]) (hQ : Q ≠ 0)
    (hT : PreservesMeshOne Q) (t : ℂ) (ht : aeval t Q = 0) :
    t.im = 0 ∧ 0 ≤ t.re := by
  by_contra hbad
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hbad ⟨by simp, by simp⟩
  have h1t : (1 - t) ≠ 0 := sub_ne_zero.2 (Ne.symm ht1)
  set x : ℂ := 1 / (1 - t) with hx
  have hx0 : x ≠ 0 := by simp [hx, h1t]
  have hSx : (limitPoly Q).eval x = 0 := by
    rw [hx, eval_limitPoly_inv Q t ht1, ht, mul_zero]
  have htx : t = 1 - 1 / x := by
    rw [hx]; field_simp; ring
  have key := limitPoly_no_bad_root Q hQ hT x.re x.im
  rw [Complex.re_add_im] at key
  refine key ?_ hSx
  by_cases him : x.im = 0
  · right
    refine ⟨him, ?_⟩
    have hxr : x = (x.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hre0 : x.re ≠ 0 := by
      intro h; apply hx0; rw [hxr, h]; simp
    have ht' : t = ((1 - 1 / x.re : ℝ) : ℂ) := by
      rw [htx]; nth_rw 1 [hxr]; push_cast; ring
    have htim : t.im = 0 := by rw [ht']; simp
    have htre : t.re = 1 - 1 / x.re := by rw [ht']; simp
    have hneg : t.re < 0 := by
      by_contra hh; exact hbad ⟨htim, le_of_not_gt hh⟩
    rw [htre] at hneg
    have hpos : 1 < 1 / x.re := by linarith
    have hxpos : 0 < x.re := by
      by_contra hh
      have : 1 / x.re ≤ 0 := by
        apply div_nonpos_of_nonneg_of_nonpos <;> linarith
      linarith
    refine ⟨hxpos, ?_⟩
    rw [lt_div_iff₀ hxpos] at hpos
    linarith
  · left; exact him

private lemma card_roots_of_complex_real (Q : ℝ[X])
    (h : ∀ t : ℂ, aeval t Q = 0 → t.im = 0) :
    Q.roots.card = Q.natDegree := by
  induction hn : Q.natDegree generalizing Q with
  | zero =>
    rw [eq_C_of_natDegree_eq_zero hn, roots_C]; rfl
  | succ n ih =>
    have hQ0 : Q ≠ 0 := by rintro rfl; simp at hn
    have hdeg : 0 < (Q.map (algebraMap ℝ ℂ)).degree := by
      rw [degree_map]; apply natDegree_pos_iff_degree_pos.1; lia
    obtain ⟨z, hz⟩ := Complex.exists_root hdeg
    have hz' : aeval z Q = 0 := by rw [aeval_def, ← eval_map]; exact hz
    have hzim := h z hz'
    have hzr : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hzim]
    have hroot : Q.IsRoot z.re := by
      have h2 := aeval_algebraMap_apply ℂ z.re Q
      rw [coe_aeval_eq_eval] at h2
      rw [IsRoot.def]
      have : (algebraMap ℝ ℂ) (eval z.re Q) = 0 := by
        rw [← h2]; simpa [← hzr] using hz'
      simpa using this
    set Q' := Q /ₘ (X - C z.re) with hQ'
    have hfac : (X - C z.re) * Q' = Q := mul_divByMonic_eq_iff_isRoot.2 hroot
    have hQ'0 : Q' ≠ 0 := by rintro h0; rw [h0, mul_zero] at hfac; exact hQ0 hfac.symm
    have hdegQ' : Q'.natDegree = n := by
      have := congrArg natDegree hfac
      rw [natDegree_mul (X_sub_C_ne_zero _) hQ'0, natDegree_X_sub_C] at this
      lia
    have ih' := ih Q' (fun t ht => h t (by rw [← hfac, map_mul, ht, mul_zero])) hdegQ'
    rw [← hfac, roots_mul (by rw [hfac]; exact hQ0), roots_X_sub_C, Multiset.card_add, ih']
    simp; lia


/-- **Discrete Hermite--Poulain theorem, necessity** (BKS 2016, Theorem 3; formalized by
Aristotle (Harmonic)).  If the finite-difference operator `p ↦ ∑ₖ aₖ p(x - k)` with symbol `Q`
maps polynomials of mesh at least one to polynomials of mesh at least one, then all zeros of
`Q` are real and nonnegative. -/
theorem hasOnlyNonnegRoots_of_forall_finiteDifferenceOp_meshGE {Q : ℝ[X]}
    (hT : ∀ p : ℝ[X], p.MeshGE 1 → (finiteDifferenceOp 1 Q p).MeshGE 1) :
    HasOnlyNonnegRoots Q := by
  by_cases hQ : Q = 0
  · exact Or.inl hQ
  refine Or.inr ⟨splits_iff_card_roots.2 (card_roots_of_complex_real Q fun t ht =>
    (complex_root_good Q hQ hT t ht).1), fun t ht => ?_⟩
  have h0 : aeval (t : ℂ) Q = 0 := by
    have h1 := ((mem_roots hQ).1 ht).eq_zero
    have h2 := aeval_algebraMap_apply ℂ t Q
    rw [coe_aeval_eq_eval, h1, map_zero] at h2
    simpa using h2
  simpa using (complex_root_good Q hQ hT t h0).2

/-- **The discrete Hermite--Poulain theorem** (BKS 2016, Theorem 3).  The operator
`p ↦ ∑ₖ aₖ p(x - k)` with symbol `Q` maps polynomials of mesh at least one to polynomials of
mesh at least one if and only if every zero of `Q` is real and nonnegative. -/
theorem forall_finiteDifferenceOp_meshGE_one_iff {Q : ℝ[X]} :
    (∀ p : ℝ[X], p.MeshGE 1 → (finiteDifferenceOp 1 Q p).MeshGE 1) ↔ HasOnlyNonnegRoots Q :=
  ⟨hasOnlyNonnegRoots_of_forall_finiteDifferenceOp_meshGE, fun hQ _ hp =>
    finiteDifferenceOp_meshGE one_pos hQ hp le_rfl⟩

private lemma finiteDifferenceOp_comp_C_mul_X {α : ℝ} (hα : 0 < α) (Q p : ℝ[X]) :
    finiteDifferenceOp α Q (p.comp (C α⁻¹ * X)) =
      (finiteDifferenceOp 1 Q p).comp (C α⁻¹ * X) := by
  induction Q using Polynomial.induction_on' with
  | add q r hq hr => rw [finiteDifferenceOp_add, hq, hr, finiteDifferenceOp_add, add_comp]
  | monomial n a =>
    have hcomp : (X - C ((n : ℝ) * 1)).comp (C α⁻¹ * X) =
        (C α⁻¹ * X).comp (X - C ((n : ℝ) * α)) := by
      simp only [sub_comp, X_comp, C_comp, mul_comp, mul_sub, ← C_mul]
      rw [show α⁻¹ * ((n : ℝ) * α) = (n : ℝ) * 1 by field_simp]
    simp only [finiteDifferenceOp_monomial, mul_comp, C_comp, comp_assoc, hcomp]

/-- **The discrete Hermite--Poulain theorem for a general step** (BKS 2016, Theorem 3).  For
`α > 0`, the operator `p ↦ ∑ₖ aₖ p(x - kα)` with symbol `Q` maps polynomials of mesh at least
`α` to polynomials of mesh at least `α` if and only if every zero of `Q` is real and
nonnegative. -/
theorem forall_finiteDifferenceOp_meshGE_iff {α : ℝ} {Q : ℝ[X]} (hα : 0 < α) :
    (∀ p : ℝ[X], p.MeshGE α → (finiteDifferenceOp α Q p).MeshGE α) ↔ HasOnlyNonnegRoots Q := by
  refine ⟨fun hT => hasOnlyNonnegRoots_of_forall_finiteDifferenceOp_meshGE fun p hp => ?_,
    fun hQ _ hp => finiteDifferenceOp_meshGE hα hQ hp le_rfl⟩
  have h1 : (p.comp (C α⁻¹ * X)).MeshGE α := by
    simpa using hp.comp_C_mul_X (inv_pos.2 hα)
  have h2 := (hT _ h1).comp_C_mul_X hα
  rw [finiteDifferenceOp_comp_C_mul_X hα, div_self hα.ne', comp_assoc] at h2
  simpa [mul_comp, ← mul_assoc, ← C_mul, hα.ne'] using h2

end

end RealRooted
