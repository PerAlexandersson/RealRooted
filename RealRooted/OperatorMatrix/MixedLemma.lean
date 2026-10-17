import RealRooted.OperatorMatrix.Directed
import RealRooted.RootPolynomial

/-!
# The mixed differential lemma

For PF polynomials with `p ≤ q` (directed interlacing `Interl p q`, zeros and repeated roots
allowed), `p' + q' ≤ q + X p'`
(`interl_derivative_add_derivative_add_X_mul_derivative`).  The coprime, strictly interlacing
case is `interl_derivative_add_derivative_add_X_mul_derivative_of_isCoprime`; the general case
follows by separating the merged ordered root lists, applying the strict case, and passing to the
coefficientwise limit with `interl_of_pf_coeff_tendsto_of_natDegree_le`.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

private def separateEven (eps : ℝ) : List ℝ → List ℝ
  | [] => []
  | x :: xs =>
      (x - eps * (2 * (xs.length + 1) : ℝ)) :: separateEven eps xs

private def separateOdd (eps : ℝ) : List ℝ → List ℝ
  | [] => []
  | x :: xs =>
      (x - eps * (2 * xs.length + 1 : ℝ)) :: separateOdd eps xs

private def mergeInter : List ℝ → List ℝ → List ℝ
  | [], rs => rs
  | s :: ss, r₁ :: r₂ :: rs => r₁ :: s :: mergeInter ss (r₂ :: rs)
  | ss, rs => ss ++ rs

private def mergeAlt : List ℝ → List ℝ → List ℝ
  | [], rs => rs
  | s :: ss, r :: rs => s :: mergeInter ss (r :: rs)
  | ss, rs => ss ++ rs

private lemma length_separateEven (eps : ℝ) (xs : List ℝ) :
    (separateEven eps xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [separateEven, ih]

private lemma length_separateOdd (eps : ℝ) (xs : List ℝ) :
    (separateOdd eps xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [separateOdd, ih]

private lemma separateEven_zero (xs : List ℝ) : separateEven 0 xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [separateEven, ih]

private lemma separateOdd_zero (xs : List ℝ) : separateOdd 0 xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [separateOdd, ih]

private lemma mergeInter_separated_head (eps r : ℝ) (ss rs : List ℝ)
    (hlen : ss.length = rs.length) :
    ∃ tail, mergeInter (separateEven eps ss) (separateOdd eps (r :: rs)) =
      (r - eps * (2 * rs.length + 1 : ℝ)) :: tail := by
  cases ss with
  | nil =>
    have hrs : rs = [] := by simpa using hlen.symm
    subst rs
    simp [separateEven, separateOdd, mergeInter]
  | cons s ss =>
    cases rs with
    | nil => simp at hlen
    | cons r₂ rs => simp [separateEven, separateOdd, mergeInter]

private lemma separated_listInterlaces
    {ss rs : List ℝ} {eps : ℝ} (heps : 0 < eps)
    (hlen : ss.length + 1 = rs.length) (hint : ListInterlaces ss rs) :
    ListInterlaces (separateEven eps ss) (separateOdd eps rs) ∧
      (mergeInter (separateEven eps ss) (separateOdd eps rs)).Pairwise (· < ·) := by
  induction ss generalizing rs with
  | nil =>
      cases rs with
      | nil => simp at hlen
      | cons r rs =>
        have hrs : rs = [] := by simpa using hlen
        subst rs
        simp [separateEven, separateOdd, mergeInter, ListInterlaces]
  | cons s ss ih =>
      cases rs with
      | nil => simp at hlen
      | cons r₁ rs =>
        cases rs with
        | nil => simp [ListInterlaces] at hint
        | cons r₂ rs =>
          have hlen' : ss.length + 1 = (r₂ :: rs).length := by simpa using hlen
          rcases hint with ⟨hr₁s, hsr₂, htail⟩
          obtain ⟨ihInter, ihPair⟩ := ih hlen' htail
          have hlenTail : ss.length = rs.length := by simpa using hlen'
          have hr₁s' :
              r₁ - eps * (2 * (r₂ :: rs).length + 1 : ℝ) <
                s - eps * (2 * (ss.length + 1) : ℝ) := by
            rw [hlenTail]
            simp only [List.length_cons]
            push_cast
            nlinarith
          have hsr₂' :
              s - eps * (2 * (ss.length + 1) : ℝ) <
                r₂ - eps * (2 * rs.length + 1 : ℝ) := by
            rw [hlenTail]
            nlinarith
          have htailAll : ∀ x ∈ mergeInter (separateEven eps ss)
              (separateOdd eps (r₂ :: rs)),
              s - eps * (2 * (ss.length + 1) : ℝ) < x := by
            intro x hx
            obtain ⟨tail, hmerge⟩ :=
              mergeInter_separated_head eps r₂ ss rs hlenTail
            rw [hmerge] at hx ihPair
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hsr₂'
            · exact lt_trans hsr₂' ((List.pairwise_cons.mp ihPair).1 x hx)
          have hr₁All : ∀ x ∈
              (s - eps * (2 * (ss.length + 1) : ℝ)) ::
                mergeInter (separateEven eps ss) (separateOdd eps (r₂ :: rs)),
              r₁ - eps * (2 * (r₂ :: rs).length + 1 : ℝ) < x := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hr₁s'
            · exact lt_trans hr₁s' (htailAll x hx)
          refine ⟨?_, ?_⟩
          · exact ⟨hr₁s'.le, hsr₂'.le, ihInter⟩
          · simp only [separateEven, separateOdd, mergeInter]
            exact List.pairwise_cons.mpr
              ⟨hr₁All, List.pairwise_cons.mpr ⟨htailAll, ihPair⟩⟩

private lemma separated_listAlternates
    {ss rs : List ℝ} {eps : ℝ} (heps : 0 < eps)
    (hlen : ss.length = rs.length) (halt : ListAlternates ss rs) :
    ListAlternates (separateEven eps ss) (separateOdd eps rs) ∧
      (mergeAlt (separateEven eps ss) (separateOdd eps rs)).Pairwise (· < ·) := by
  cases ss with
  | nil =>
    have hrs : rs = [] := by simpa using hlen.symm
    subst rs
    simp [separateEven, separateOdd, mergeAlt, ListAlternates]
  | cons s ss =>
    cases rs with
    | nil => simp at hlen
    | cons r rs =>
      rcases halt with ⟨hsr, htail⟩
      have hlen' : ss.length + 1 = (r :: rs).length := by simpa using hlen
      obtain ⟨htailInter, htailPair⟩ :=
        separated_listInterlaces heps hlen' htail
      have hsr' :
          s - eps * (2 * (ss.length + 1) : ℝ) <
            r - eps * (2 * rs.length + 1 : ℝ) := by
        have hlenTail : ss.length = rs.length := by simpa using hlen
        rw [hlenTail]
        nlinarith
      have hsAll : ∀ x ∈ mergeInter (separateEven eps ss)
          (separateOdd eps (r :: rs)),
          s - eps * (2 * (ss.length + 1) : ℝ) < x := by
        intro x hx
        have hlenTail : ss.length = rs.length := by simpa using hlen
        obtain ⟨tail, hmerge⟩ :=
          mergeInter_separated_head eps r ss rs hlenTail
        rw [hmerge] at hx htailPair
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hsr'
        · exact lt_trans hsr' ((List.pairwise_cons.mp htailPair).1 x hx)
      refine ⟨⟨hsr'.le, htailInter⟩, ?_⟩
      simp only [separateEven, separateOdd, mergeAlt]
      exact List.pairwise_cons.mpr ⟨hsAll, htailPair⟩

private lemma mergeInter_perm_append {ss rs : List ℝ}
    (hint : ListInterlaces ss rs) : List.Perm (mergeInter ss rs) (ss ++ rs) := by
  induction ss generalizing rs with
  | nil => simp [mergeInter]
  | cons s ss ih =>
      cases rs with
      | nil => simp [ListInterlaces] at hint
      | cons r₁ rs =>
        cases rs with
        | nil => simp [ListInterlaces] at hint
        | cons r₂ rs =>
          rcases hint with ⟨_, _, htail⟩
          have hperm := ih htail
          have hswap : List.Perm (r₁ :: s :: mergeInter ss (r₂ :: rs))
              (s :: r₁ :: mergeInter ss (r₂ :: rs)) :=
            (List.Perm.swap r₁ s _).symm
          have htailPerm : List.Perm (s :: r₁ :: mergeInter ss (r₂ :: rs))
              (s :: r₁ :: (ss ++ r₂ :: rs)) := (hperm.cons r₁).cons s
          have hmiddle : List.Perm (s :: r₁ :: (ss ++ r₂ :: rs))
              (s :: (ss ++ r₁ :: r₂ :: rs)) := List.Perm.cons s List.perm_middle.symm
          exact hswap.trans (htailPerm.trans hmiddle)

private lemma mergeAlt_perm_append {ss rs : List ℝ}
    (halt : ListAlternates ss rs) : List.Perm (mergeAlt ss rs) (ss ++ rs) := by
  cases ss with
  | nil =>
    cases rs with
    | nil => simp [mergeAlt]
    | cons r rs => simp [ListAlternates] at halt
  | cons s ss =>
    cases rs with
    | nil => simp [ListAlternates] at halt
    | cons r rs => exact (mergeInter_perm_append halt.2).cons s

private lemma mergeInter_component_sublist {ss rs : List ℝ}
    (hint : ListInterlaces ss rs) :
    List.Sublist ss (mergeInter ss rs) ∧ List.Sublist rs (mergeInter ss rs) := by
  induction ss generalizing rs with
  | nil => simp [mergeInter]
  | cons s ss ih =>
      cases rs with
      | nil => simp [ListInterlaces] at hint
      | cons r₁ rs =>
        cases rs with
        | nil => simp [ListInterlaces] at hint
        | cons r₂ rs =>
          obtain ⟨_, _, htail⟩ := hint
          obtain ⟨hleft, hright⟩ := ih htail
          constructor
          · exact List.Sublist.cons r₁ (List.Sublist.cons_cons s hleft)
          · exact List.Sublist.cons_cons r₁ (List.Sublist.cons s hright)

private lemma mergeAlt_component_sublist {ss rs : List ℝ}
    (halt : ListAlternates ss rs) :
    List.Sublist ss (mergeAlt ss rs) ∧ List.Sublist rs (mergeAlt ss rs) := by
  cases ss with
  | nil =>
    cases rs with
    | nil => simp [mergeAlt]
    | cons r rs => simp [ListAlternates] at halt
  | cons s ss =>
    cases rs with
    | nil => simp [ListAlternates] at halt
    | cons r rs =>
      obtain ⟨hleft, hright⟩ := mergeInter_component_sublist halt.2
      exact ⟨List.Sublist.cons_cons s hleft, List.Sublist.cons s hright⟩

private lemma separated_lists_of_listInterlaces
    {ss rs : List ℝ} {eps : ℝ} (heps : 0 < eps)
    (hlen : ss.length + 1 = rs.length) (hint : ListInterlaces ss rs) :
    ListInterlaces (separateEven eps ss) (separateOdd eps rs) ∧
      (separateEven eps ss).Pairwise (· ≤ ·) ∧
      (separateOdd eps rs).Pairwise (· ≤ ·) ∧
      (separateEven eps ss).Disjoint (separateOdd eps rs) := by
  obtain ⟨hinter, hpair⟩ := separated_listInterlaces heps hlen hint
  have hperm := mergeInter_perm_append hinter
  have hsubs := mergeInter_component_sublist hinter
  have happNodup : (separateEven eps ss ++ separateOdd eps rs).Nodup :=
    (hperm.nodup_iff.mp hpair.nodup)
  have hparts := List.nodup_append'.mp happNodup
  exact ⟨hinter, (hpair.sublist hsubs.1).imp le_of_lt,
    (hpair.sublist hsubs.2).imp le_of_lt, hparts.2.2⟩

private lemma separated_lists_of_listAlternates
    {ss rs : List ℝ} {eps : ℝ} (heps : 0 < eps)
    (hlen : ss.length = rs.length) (halt : ListAlternates ss rs) :
    ListAlternates (separateEven eps ss) (separateOdd eps rs) ∧
      (separateEven eps ss).Pairwise (· ≤ ·) ∧
      (separateOdd eps rs).Pairwise (· ≤ ·) ∧
      (separateEven eps ss).Disjoint (separateOdd eps rs) := by
  obtain ⟨hinter, hpair⟩ := separated_listAlternates heps hlen halt
  have hperm := mergeAlt_perm_append hinter
  have hsubs := mergeAlt_component_sublist hinter
  have happNodup : (separateEven eps ss ++ separateOdd eps rs).Nodup :=
    (hperm.nodup_iff.mp hpair.nodup)
  have hparts := List.nodup_append'.mp happNodup
  exact ⟨hinter, (hpair.sublist hsubs.1).imp le_of_lt,
    (hpair.sublist hsubs.2).imp le_of_lt, hparts.2.2⟩

private lemma separateEven_neg {eps : ℝ} (heps : 0 < eps) {xs : List ℝ}
    (hxs : ∀ x ∈ xs, x ≤ 0) : ∀ x ∈ separateEven eps xs, x < 0 := by
  induction xs with
  | nil => simp [separateEven]
  | cons y ys ih =>
      intro x hx
      simp only [separateEven, List.mem_cons] at hx
      rcases hx with rfl | hx
      · have hy := hxs y (List.mem_cons_self ..)
        have hlen : 0 < (2 * (ys.length + 1) : ℝ) := by positivity
        nlinarith
      · exact ih (fun z hz => hxs z (List.mem_cons_of_mem y hz)) x hx

private lemma separateOdd_neg {eps : ℝ} (heps : 0 < eps) {xs : List ℝ}
    (hxs : ∀ x ∈ xs, x ≤ 0) : ∀ x ∈ separateOdd eps xs, x < 0 := by
  induction xs with
  | nil => simp [separateOdd]
  | cons y ys ih =>
      intro x hx
      simp only [separateOdd, List.mem_cons] at hx
      rcases hx with rfl | hx
      · have hy := hxs y (List.mem_cons_self ..)
        have hlen : 0 < (2 * ys.length + 1 : ℝ) := by positivity
        nlinarith
      · exact ih (fun z hz => hxs z (List.mem_cons_of_mem y hz)) x hx

private def rootApproxEven (c : ℝ) (xs : List ℝ) (eps : ℝ) : ℝ[X] :=
  C c * rootPolynomial (separateEven eps xs : Multiset ℝ)

private def rootApproxOdd (c : ℝ) (xs : List ℝ) (eps : ℝ) : ℝ[X] :=
  C c * rootPolynomial (separateOdd eps xs : Multiset ℝ)

private lemma continuous_coeff_rootPolynomial_separateEven (xs : List ℝ) :
    ∀ i, Continuous fun eps : ℝ =>
      (rootPolynomial (separateEven eps xs : Multiset ℝ)).coeff i := by
  induction xs with
  | nil =>
      intro i
      simpa [separateEven, rootPolynomial] using
        (continuous_const : Continuous fun _ : ℝ => (1 : ℝ[X]).coeff i)
  | cons x xs ih =>
      intro i
      cases i with
      | zero =>
        change Continuous fun eps : ℝ =>
          ((X - C (x - eps * (2 * (xs.length + 1) : ℝ))) *
            rootPolynomial (separateEven eps xs : Multiset ℝ)).coeff 0
        simp only [coeff_X_sub_C_mul, ite_true, zero_sub]
        have hlinear : Continuous fun eps : ℝ =>
            x - eps * (2 * (xs.length + 1) : ℝ) :=
          continuous_const.sub (continuous_id.mul continuous_const)
        exact (hlinear.mul (ih 0)).neg
      | succ i =>
        change Continuous fun eps : ℝ =>
          ((X - C (x - eps * (2 * (xs.length + 1) : ℝ))) *
            rootPolynomial (separateEven eps xs : Multiset ℝ)).coeff (i + 1)
        simp only [coeff_X_sub_C_mul, Nat.add_sub_cancel]
        have hlinear : Continuous fun eps : ℝ =>
            x - eps * (2 * (xs.length + 1) : ℝ) :=
          continuous_const.sub (continuous_id.mul continuous_const)
        exact (ih i).sub (hlinear.mul (ih (i + 1)))

private lemma continuous_coeff_rootPolynomial_separateOdd (xs : List ℝ) :
    ∀ i, Continuous fun eps : ℝ =>
      (rootPolynomial (separateOdd eps xs : Multiset ℝ)).coeff i := by
  induction xs with
  | nil =>
      intro i
      simpa [separateOdd, rootPolynomial] using
        (continuous_const : Continuous fun _ : ℝ => (1 : ℝ[X]).coeff i)
  | cons x xs ih =>
      intro i
      cases i with
      | zero =>
        change Continuous fun eps : ℝ =>
          ((X - C (x - eps * (2 * xs.length + 1 : ℝ))) *
            rootPolynomial (separateOdd eps xs : Multiset ℝ)).coeff 0
        simp only [coeff_X_sub_C_mul, ite_true, zero_sub]
        have hlinear : Continuous fun eps : ℝ =>
            x - eps * (2 * xs.length + 1 : ℝ) :=
          continuous_const.sub (continuous_id.mul continuous_const)
        exact (hlinear.mul (ih 0)).neg
      | succ i =>
        change Continuous fun eps : ℝ =>
          ((X - C (x - eps * (2 * xs.length + 1 : ℝ))) *
            rootPolynomial (separateOdd eps xs : Multiset ℝ)).coeff (i + 1)
        simp only [coeff_X_sub_C_mul, Nat.add_sub_cancel]
        have hlinear : Continuous fun eps : ℝ =>
            x - eps * (2 * xs.length + 1 : ℝ) :=
          continuous_const.sub (continuous_id.mul continuous_const)
        exact (ih i).sub (hlinear.mul (ih (i + 1)))

private lemma continuous_coeff_rootApproxEven (c : ℝ) (xs : List ℝ) (i : ℕ) :
    Continuous fun eps : ℝ => (rootApproxEven c xs eps).coeff i := by
  simp only [rootApproxEven, coeff_C_mul]
  exact continuous_const.mul (continuous_coeff_rootPolynomial_separateEven xs i)

private lemma continuous_coeff_rootApproxOdd (c : ℝ) (xs : List ℝ) (i : ℕ) :
    Continuous fun eps : ℝ => (rootApproxOdd c xs eps).coeff i := by
  simp only [rootApproxOdd, coeff_C_mul]
  exact continuous_const.mul (continuous_coeff_rootPolynomial_separateOdd xs i)

private lemma C_mul_rootPolynomial_ne_zero {c : ℝ} (hc : c ≠ 0) (s : Multiset ℝ) :
    C c * rootPolynomial s ≠ 0 :=
  mul_ne_zero (C_ne_zero.mpr hc) (rootPolynomial_ne_zero s)

private lemma C_mul_rootPolynomial_splits (c : ℝ) (s : Multiset ℝ) :
    (C c * rootPolynomial s).Splits :=
  (rootPolynomial_splits s).C_mul c

private lemma roots_C_mul_rootPolynomial {c : ℝ} (hc : c ≠ 0) (s : Multiset ℝ) :
    (C c * rootPolynomial s).roots = s := by
  rw [roots_C_mul _ hc, roots_rootPolynomial]

private lemma natDegree_C_mul_rootPolynomial {c : ℝ} (hc : c ≠ 0)
    (s : Multiset ℝ) :
    (C c * rootPolynomial s).natDegree = s.card := by
  rw [natDegree_C_mul hc, natDegree_rootPolynomial]

private lemma isPFPolynomial_C_mul_rootPolynomial {c : ℝ} (hc : 0 < c)
    {s : Multiset ℝ} (hs : ∀ r ∈ s, r ≤ 0) :
    IsPFPolynomial (C c * rootPolynomial s) := by
  apply IsPFPolynomial.of_realRooted_nonneg
  · exact (hasNonnegCoeffs_C hc.le).mul (by
      simpa only [rootPolynomial] using hasNonnegCoeffs_multiset_prod_X_sub_C s hs)
  · exact C_mul_rootPolynomial_splits c s

private lemma eval_zero_C_mul_rootPolynomial_pos {c : ℝ} (hc : 0 < c)
    {s : Multiset ℝ} (hs : ∀ r ∈ s, r < 0) :
    0 < (C c * rootPolynomial s).eval 0 := by
  rw [eval_mul, eval_C, rootPolynomial, eval_multiset_prod, Multiset.map_map]
  apply mul_pos hc
  apply Multiset.prod_pos
  intro y hy
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C, zero_sub]
  exact neg_pos.mpr (hs r hr)

private lemma strictInterl_rootApproximations
    {c d eps : ℝ} (hc : c ≠ 0) (hd : d ≠ 0) (heps : 0 < eps)
    {ss rs : List ℝ}
    (hshape : (ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
      (ss.length = rs.length ∧ ListAlternates ss rs)) :
    StrictInterl (rootApproxEven c ss eps) (rootApproxOdd d rs eps) ∧
      (separateEven eps ss).Disjoint (separateOdd eps rs) := by
  rcases hshape with ⟨hlen, hinter⟩ | ⟨hlen, hinter⟩
  · obtain ⟨hinter', hss, hrs, hdisjoint⟩ :=
      separated_lists_of_listInterlaces heps hlen hinter
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, separateEven eps ss, separateOdd eps rs,
      hss, hrs, ?_, ?_, Or.inl ⟨?_, hinter'⟩⟩, hdisjoint⟩
    · exact C_mul_rootPolynomial_ne_zero hc _
    · exact C_mul_rootPolynomial_splits c _
    · exact C_mul_rootPolynomial_ne_zero hd _
    · exact C_mul_rootPolynomial_splits d _
    · exact (roots_C_mul_rootPolynomial hc _).symm
    · exact (roots_C_mul_rootPolynomial hd _).symm
    · simpa only [length_separateEven, length_separateOdd] using hlen
  · obtain ⟨hinter', hss, hrs, hdisjoint⟩ :=
      separated_lists_of_listAlternates heps hlen hinter
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, separateEven eps ss, separateOdd eps rs,
      hss, hrs, ?_, ?_, Or.inr ⟨?_, hinter'⟩⟩, hdisjoint⟩
    · exact C_mul_rootPolynomial_ne_zero hc _
    · exact C_mul_rootPolynomial_splits c _
    · exact C_mul_rootPolynomial_ne_zero hd _
    · exact C_mul_rootPolynomial_splits d _
    · exact (roots_C_mul_rootPolynomial hc _).symm
    · exact (roots_C_mul_rootPolynomial hd _).symm
    · simpa only [length_separateEven, length_separateOdd] using hlen

/-- The weak directed mixed differential comparison for an interlacing PF pair. -/
theorem interl_derivative_add_derivative_add_X_mul_derivative {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Interl p q) :
    Interl (p.derivative + q.derivative) (q + X * p.derivative) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simpa only [derivative_zero, zero_add, mul_zero, add_zero] using
      hq.interl_derivative_self
  rcases eq_or_ne q 0 with rfl | hq0
  · simp only [derivative_zero, add_zero, zero_add]
    apply (interl_iff_interl_X_mul hp.derivative hp.derivative).mp
    exact Interl.refl fun hne => (hp.derivative.ne_zero_and_splits hne).2
  have hpqStrict := hpq.toStrictInterl_of_ne hp0 hq0
  rcases hpqStrict with
    ⟨hpReal, hqReal, ss, rs, hss, hrs, hssRoots, hrsRoots, hshape⟩
  have hpLeading : 0 < p.leadingCoeff :=
    hp.hasNonnegCoeffs.pos_leadingCoeff hp0
  have hqLeading : 0 < q.leadingCoeff :=
    hq.hasNonnegCoeffs.pos_leadingCoeff hq0
  have hssNonpos : ∀ r ∈ ss, r ≤ 0 := by
    intro r hr
    apply hp.roots_nonpos r
    rw [← hssRoots]
    exact Multiset.mem_coe.mpr hr
  have hrsNonpos : ∀ r ∈ rs, r ≤ 0 := by
    intro r hr
    apply hq.roots_nonpos r
    rw [← hrsRoots]
    exact Multiset.mem_coe.mpr hr
  let delta : ℕ → ℝ := fun M => ((M : ℝ) + 1)⁻¹
  have hdeltaPos (M : ℕ) : 0 < delta M := by
    simp only [delta]
    positivity
  have hdelta : Tendsto delta atTop (nhds 0) := by
    simpa only [delta, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let pM : ℕ → ℝ[X] := fun M => rootApproxEven p.leadingCoeff ss (delta M)
  let qM : ℕ → ℝ[X] := fun M => rootApproxOdd q.leadingCoeff rs (delta M)
  have hpair (M : ℕ) : StrictInterl (pM M) (qM M) ∧
      (separateEven (delta M) ss).Disjoint (separateOdd (delta M) rs) := by
    exact strictInterl_rootApproximations hpLeading.ne' hqLeading.ne'
      (hdeltaPos M) hshape
  have hpMRoots (M : ℕ) :
      (pM M).roots = (separateEven (delta M) ss : Multiset ℝ) := by
    exact roots_C_mul_rootPolynomial hpLeading.ne' _
  have hqMRoots (M : ℕ) :
      (qM M).roots = (separateOdd (delta M) rs : Multiset ℝ) := by
    exact roots_C_mul_rootPolynomial hqLeading.ne' _
  have hpMPF (M : ℕ) : IsPFPolynomial (pM M) := by
    apply isPFPolynomial_C_mul_rootPolynomial hpLeading
    intro r hr
    apply (separateEven_neg (hdeltaPos M) hssNonpos r
      (Multiset.mem_coe.mp hr)).le
  have hqMPF (M : ℕ) : IsPFPolynomial (qM M) := by
    apply isPFPolynomial_C_mul_rootPolynomial hqLeading
    intro r hr
    apply (separateOdd_neg (hdeltaPos M) hrsNonpos r
      (Multiset.mem_coe.mp hr)).le
  have hpMZero (M : ℕ) : 0 < (pM M).eval 0 := by
    apply eval_zero_C_mul_rootPolynomial_pos hpLeading
    intro r hr
    exact separateEven_neg (hdeltaPos M) hssNonpos r (Multiset.mem_coe.mp hr)
  have hqMZero (M : ℕ) : 0 < (qM M).eval 0 := by
    apply eval_zero_C_mul_rootPolynomial_pos hqLeading
    intro r hr
    exact separateOdd_neg (hdeltaPos M) hrsNonpos r (Multiset.mem_coe.mp hr)
  have hcoprime (M : ℕ) : IsCoprime (pM M) (qM M) := by
    apply isCoprime_of_no_common_real_root_of_isRealRooted
      (hpair M).1.1.1 (hpair M).1.1.2
    intro r hpr hqr
    have hrp : r ∈ (pM M).roots := (mem_roots (hpair M).1.1.1).mpr hpr
    have hrq : r ∈ (qM M).roots := (mem_roots (hpair M).1.2.1.1).mpr hqr
    rw [hpMRoots M] at hrp
    rw [hqMRoots M] at hrq
    exact (hpair M).2 (Multiset.mem_coe.mp hrp) (Multiset.mem_coe.mp hrq)
  have hinterl (M : ℕ) :
      Interl ((pM M).derivative + (qM M).derivative)
        (qM M + X * (pM M).derivative) :=
    interl_derivative_add_derivative_add_X_mul_derivative_of_isCoprime
      (hpMPF M) (hqMPF M) (hpair M).1 (hcoprime M) (hpMZero M) (hqMZero M)
  have hpMDegree (M : ℕ) : (pM M).natDegree = p.natDegree := by
    change (rootApproxEven p.leadingCoeff ss (delta M)).natDegree = p.natDegree
    rw [rootApproxEven, natDegree_C_mul_rootPolynomial hpLeading.ne']
    change (separateEven (delta M) ss).length = p.natDegree
    have hcard := card_roots_of_splits hpReal.2
    rw [← hssRoots] at hcard
    change ss.length = p.natDegree at hcard
    exact (length_separateEven (delta M) ss).trans hcard
  have hqMDegree (M : ℕ) : (qM M).natDegree = q.natDegree := by
    change (rootApproxOdd q.leadingCoeff rs (delta M)).natDegree = q.natDegree
    rw [rootApproxOdd, natDegree_C_mul_rootPolynomial hqLeading.ne']
    change (separateOdd (delta M) rs).length = q.natDegree
    have hcard := card_roots_of_splits hqReal.2
    rw [← hrsRoots] at hcard
    change rs.length = q.natDegree at hcard
    exact (length_separateOdd (delta M) rs).trans hcard
  have hpAtZero : rootApproxEven p.leadingCoeff ss 0 = p := by
    simp only [rootApproxEven, separateEven_zero]
    rw [hssRoots]
    exact C_leadingCoeff_mul_prod_multiset_X_sub_C
      (card_roots_of_splits hpReal.2)
  have hqAtZero : rootApproxOdd q.leadingCoeff rs 0 = q := by
    simp only [rootApproxOdd, separateOdd_zero]
    rw [hrsRoots]
    exact C_leadingCoeff_mul_prod_multiset_X_sub_C
      (card_roots_of_splits hqReal.2)
  have hpCoeff (i : ℕ) : Tendsto (fun M => (pM M).coeff i) atTop
      (nhds (p.coeff i)) := by
    have hcontinuous : ContinuousAt
        (fun eps : ℝ => (rootApproxEven p.leadingCoeff ss eps).coeff i) 0 :=
      (continuous_coeff_rootApproxEven p.leadingCoeff ss i).continuousAt
    simpa only [pM, hpAtZero, Function.comp_def] using
      hcontinuous.tendsto.comp hdelta
  have hqCoeff (i : ℕ) : Tendsto (fun M => (qM M).coeff i) atTop
      (nhds (q.coeff i)) := by
    have hcontinuous : ContinuousAt
        (fun eps : ℝ => (rootApproxOdd q.leadingCoeff rs eps).coeff i) 0 :=
      (continuous_coeff_rootApproxOdd q.leadingCoeff rs i).continuousAt
    simpa only [qM, hqAtZero, Function.comp_def] using
      hcontinuous.tendsto.comp hdelta
  let leftM : ℕ → ℝ[X] := fun M =>
    (pM M).derivative + (qM M).derivative
  let rightM : ℕ → ℝ[X] := fun M =>
    qM M + X * (pM M).derivative
  have hleftPF (M : ℕ) : IsPFPolynomial (leftM M) := by
    exact isPFPolynomial_derivative_add_derivative_of_interl
      (hpMPF M) (hqMPF M) (hpair M).1.toInterl
  have hrightPF (M : ℕ) : IsPFPolynomial (rightM M) := by
    exact isPFPolynomial_add_X_mul_derivative_of_interl
      (hpMPF M) (hqMPF M) (hpair M).1.toInterl
  have hleftDegree (M : ℕ) :
      (leftM M).natDegree ≤ max p.natDegree q.natDegree := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_derivative_le _).trans
        ((Nat.sub_le _ _).trans
          ((hpMDegree M).le.trans (Nat.le_max_left _ _)))
    · exact (natDegree_derivative_le _).trans
        ((Nat.sub_le _ _).trans
          ((hqMDegree M).le.trans (Nat.le_max_right _ _)))
  have hrightDegree (M : ℕ) :
      (rightM M).natDegree ≤ max p.natDegree q.natDegree := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (hqMDegree M).le.trans (Nat.le_max_right _ _)
    · simpa only [theta] using
        (natDegree_theta_le (pM M)).trans
          ((hpMDegree M).le.trans (Nat.le_max_left _ _))
  have hleftCoeff (i : ℕ) : Tendsto (fun M => (leftM M).coeff i) atTop
      (nhds ((p.derivative + q.derivative).coeff i)) := by
    simpa only [leftM, coeff_add, coeff_derivative] using
      ((hpCoeff (i + 1)).mul_const (i + 1 : ℝ)).add
        ((hqCoeff (i + 1)).mul_const (i + 1 : ℝ))
  have hrightCoeff (i : ℕ) : Tendsto (fun M => (rightM M).coeff i) atTop
      (nhds ((q + X * p.derivative).coeff i)) := by
    simpa only [rightM, coeff_add, coeff_X_mul_derivative] using
      (hqCoeff i).add ((hpCoeff i).const_mul (i : ℝ))
  apply interl_of_pf_coeff_tendsto_of_natDegree_le hleftPF hrightPF
    (fun M => by exact hinterl M)
    hleftDegree hrightDegree hleftCoeff hrightCoeff

end RealRooted
