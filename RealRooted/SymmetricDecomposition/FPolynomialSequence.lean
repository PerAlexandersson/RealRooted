module

public import RealRooted.SymmetricDecomposition.Theorem26

/-!
# Interlacing of `f`-transforms of half-growth sequences

If a sequence `q` has nonnegative coefficients, real roots, degrees `(j + 1) / 2` and
consecutive strict interlacing, then the transforms `fPolynomial n (q n)` interlace
consecutively (`StrictInterl.fPolynomial_sequence`).  The argument (lifted from the downstream
A059427 proof) applies the minimal-box transfer
`strictInterl_fPolynomial_of_strictInterl_of_hasNonnegCoeffs_of_minimal`, peels the extra factor
`X + 1` using that the transformed roots lie in `[-1, 0]`, and pads by powers of `X + 1`.
This covers the alternating-runs polynomials A008970, A059427 and A186370, whose transformed rows
are peak polynomials.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

private lemma alt_insert_left {r : ℝ} : ∀ (sf sg : List ℝ),
    (∀ s ∈ sf, r ≤ s) → ListAlternates sf sg → ListInterlaces sf (r :: sg)
  | [], [], _, ha => by simp [ListInterlaces]
  | [], _ :: _, _, ha => by simp [ListAlternates] at ha
  | _ :: _, [], _, ha => by simp [ListAlternates] at ha
  | s :: st, b :: rest, hroot, ha => by
      simp only [ListAlternates] at ha
      simp only [ListInterlaces]
      exact ⟨hroot s (by simp), ha.1, ha.2⟩

/-- Peels a left factor `X - C r` from a strict interlacing pair when all
    roots of the peeled polynomial lie strictly to the right of `r`. -/
lemma StrictInterl.of_mul_X_sub_C_left_of_roots_gt
    {f g : ℝ[X]} {r : ℝ}
    (hf : f ≠ 0 ∧ f.Splits) (hg : g ≠ 0 ∧ g.Splits)
    (hdegf : 0 < f.natDegree)
    (hroot : ∀ s ∈ f.roots, r < s)
    (hdeg : f.natDegree + 1 = g.natDegree)
    (h : StrictInterl ((X - C r) * f) g) : StrictInterl f g := by
  have hxf : (X - C r) * f ≠ 0 := mul_ne_zero (X_sub_C_ne_zero r) hf.1
  have hxfdeg : ((X - C r) * f).natDegree = f.natDegree + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero r) hf.1]
    simp
    ring
  rcases h with ⟨hxf_rr, hg_rr, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hsslen : ss.length = f.natDegree + 1 := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hxf_rr.2]
    rw [hxfdeg]
  have hrslen : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have hss_eq_sort : (↑(f.roots.sort (· ≤ ·)) : Multiset ℝ) = f.roots :=
    Multiset.sort_eq ..
  let sf := f.roots.sort (· ≤ ·)
  have hsf : sf.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hsflen : sf.length = f.natDegree := by
    rw [← Multiset.coe_card, show (↑sf : Multiset ℝ) = f.roots from hss_eq_sort,
      card_roots_of_splits hf.2]
  have hrootmul : ((X - C r) * f).roots = ({r} : Multiset ℝ) + f.roots := by
    rw [roots_mul hxf, roots_X_sub_C]
  have hss_perm : ss.Perm (sf.orderedInsert (· ≤ ·) r) := by
    apply Multiset.coe_eq_coe.mp
    calc
      (↑ss : Multiset ℝ) = ((X - C r) * f).roots := hss_eq
      _ = ({r} : Multiset ℝ) + f.roots := hrootmul
      _ = ({r} : Multiset ℝ) + (↑sf : Multiset ℝ) := by rw [hss_eq_sort]
      _ = (↑(sf.orderedInsert (· ≤ ·) r) : Multiset ℝ) := by
        simpa using (Multiset.coe_eq_coe.mpr
          (List.perm_orderedInsert (r := (· ≤ ·)) r sf)).symm
  have hss_is : ss = sf.orderedInsert (· ≤ ·) r :=
    List.Perm.eq_of_pairwise' hss (hsf.orderedInsert r) hss_perm
  have hsf_nonempty : sf ≠ [] := by
    intro hz
    have : f.natDegree = 0 := by simpa [sf, hz] using hsflen.symm
    lia
  obtain ⟨a, l, hsfcons⟩ := List.exists_cons_of_ne_nil hsf_nonempty
  have har : r ≤ a := by
    have ha_mem : a ∈ f.roots := by
      have : a ∈ sf := by simp [hsfcons]
      rw [← hss_eq_sort]
      exact Multiset.mem_coe.mpr this
    exact le_of_lt (hroot a ha_mem)
  have hins : sf.orderedInsert (· ≤ ·) r = r :: sf := by
    rw [hsfcons, List.orderedInsert_cons_of_le (· ≤ ·) l har]
  have hss_is' : ss = r :: sf := hss_is.trans hins
  have hlen_eq : ss.length = rs.length := by
    rw [hsslen, hrslen]
    lia
  have hshape' : sf.length + 1 = rs.length := by
    rw [hss_is'] at hlen_eq
    simpa using hlen_eq
  have hrs_nonempty : rs ≠ [] := by
    intro hz
    have hlen_zero : ss.length = 0 := by simpa [hz] using hlen_eq
    rw [hsslen] at hlen_zero
    lia
  obtain ⟨b, rest, hrscons⟩ := List.exists_cons_of_ne_nil hrs_nonempty
  have hinter : ListInterlaces sf rs := by
    rcases hshape with ⟨hlen, hi⟩ | ⟨hlen, ha⟩
    · lia
    · rw [hss_is', hrscons] at ha
      have ha' : r ≤ b ∧ ListInterlaces sf (b :: rest) := by
        simpa [ListAlternates] using ha
      simpa [hrscons] using ha'.2
  exact ⟨hf, hg, sf, rs, hsf, hrs, hss_eq_sort, hrs_eq,
    Or.inl ⟨hshape', hinter⟩⟩

/-- Adds a right factor `X - C r` to the second polynomial in a same-degree
    strict interlacing pair when both root sets lie weakly to its right. -/
lemma StrictInterl.of_mul_X_sub_C_right_of_roots_ge
    {f g : ℝ[X]} {r : ℝ}
    (hf : f ≠ 0 ∧ f.Splits) (hg : g ≠ 0 ∧ g.Splits)
    (hdeg : f.natDegree = g.natDegree)
    (hrootf : ∀ s ∈ f.roots, r ≤ s)
    (hrootg : ∀ s ∈ g.roots, r ≤ s)
    (h : StrictInterl f g) : StrictInterl f ((X - C r) * g) := by
  have hxf : (X - C r) * g ≠ 0 := mul_ne_zero (X_sub_C_ne_zero r) hg.1
  rcases h with ⟨hf_rr, hg_rr, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  let sf := f.roots.sort (· ≤ ·)
  let sg := g.roots.sort (· ≤ ·)
  have hsf : sf.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hsg : sg.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hss_eq_sort : (↑sf : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_eq_sort : (↑sg : Multiset ℝ) = g.roots := Multiset.sort_eq ..
  have hss_perm : ss.Perm sf := by
    apply Multiset.coe_eq_coe.mp
    exact hss_eq.trans hss_eq_sort.symm
  have hrs_perm : rs.Perm sg := by
    apply Multiset.coe_eq_coe.mp
    exact hrs_eq.trans hrs_eq_sort.symm
  have hss_is : ss = sf := List.Perm.eq_of_pairwise' hss hsf hss_perm
  have hrs_is : rs = sg := List.Perm.eq_of_pairwise' hrs hsg hrs_perm
  have hsf_len : sf.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq_sort, card_roots_of_splits hf.2]
  have hsg_len : sg.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq_sort, card_roots_of_splits hg.2]
  have hrsg : ∀ s ∈ sg, r ≤ s := by
    intro s hs
    have hs' : s ∈ (↑sg : Multiset ℝ) := Multiset.mem_coe.mpr hs
    rw [hrs_eq_sort] at hs'
    exact hrootg s hs'
  have hnew_roots : ((↑(r :: sg) : Multiset ℝ)) = ((X - C r) * g).roots := by
    rw [roots_mul hxf, roots_X_sub_C]
    rw [← hrs_eq_sort]
    simp
  refine ⟨hf_rr, ⟨hxf, (Polynomial.Splits.X_sub_C r).mul hg.2⟩,
    sf, r :: sg, hsf, ?_, hss_eq_sort, hnew_roots, ?_⟩
  · simp only [List.pairwise_cons]
    exact ⟨hrsg, hsg⟩
  · have hlen0 : sf.length = sg.length := by
      rw [hsf_len, hsg_len, hdeg]
    rcases hshape with ⟨hbad, hi⟩ | ⟨heq, ha⟩
    · have hbad' : sf.length + 1 = sg.length := by
        simpa [hss_is, hrs_is] using hbad
      lia
    · have ha' : ListAlternates sf sg := by
        simpa [hss_is, hrs_is] using ha
      have hrootsf : ∀ s ∈ sf, r ≤ s := by
        intro s hs
        have hs' : s ∈ (↑sf : Multiset ℝ) := Multiset.mem_coe.mpr hs
        rw [hss_eq_sort] at hs'
        exact hrootf s hs'
      exact Or.inl ⟨by simp [hlen0], alt_insert_left (r := r) sf sg hrootsf ha'⟩

/-- Raises a strict interlacing relation by padding the two `f`-polynomials
    with a common power of `X + 1`. -/
lemma StrictInterl.fPolynomial_pad_of_mul_X_add_one
    {u v : ℝ[X]} {m k : ℕ}
    (hu_deg : u.natDegree ≤ m) (hv_deg : v.natDegree ≤ m)
    (hmk : m ≤ k)
    (huv : StrictInterl (fPolynomial m u) ((X + 1) * fPolynomial m v)) :
    StrictInterl (fPolynomial k u) (fPolynomial (k + 1) v) := by
  have hcommon :=
    (strictInterl_iff_strictInterl_mul_X_add_one_pow_both (n := k - m)).mpr huv
  have hleft : fPolynomial k u = (X + 1) ^ (k - m) * fPolynomial m u :=
    fPolynomial_pad_by_X_add_one_pow hu_deg hmk
  have hright : fPolynomial (k + 1) v =
      (X + 1) ^ (k - m) * ((X + 1) * fPolynomial m v) := by
    rw [fPolynomial_pad_by_X_add_one_pow hv_deg (by lia)]
    rw [show k + 1 - m = (k - m) + 1 by lia, pow_succ]
    ring
  rw [hleft, hright]
  simpa [sub_eq_add_neg] using hcommon

private lemma fPolynomial_roots_ge_neg_one
    {d : ℕ} {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ d) (hp0 : p ≠ 0) (hps : p.Splits)
    (hpnn : HasNonnegCoeffs p) :
    ∀ s ∈ (fPolynomial d p).roots, (-1 : ℝ) ≤ s := by
  intro s hs
  rw [roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
    hpdeg hp0 hps hpnn] at hs
  rcases Multiset.mem_add.mp hs with hs | hs
  · have hs' : s = (-1 : ℝ) := (Multiset.mem_replicate.mp hs).2
    simp [hs']
  · rcases Multiset.mem_map.mp hs with ⟨r, hr, rfl⟩
    exact le_of_lt (neg_one_lt_transformedRoot
      (roots_nonpos_of_hasNonnegCoeffs hpnn r hr))

/-- Transfers consecutive strict interlacing through the `f`-polynomial
    transform for a nonnegative, split, nonzero sequence with the
    half-growth degree pattern. -/
theorem StrictInterl.fPolynomial_sequence
    (q : ℕ → ℝ[X])
    (hq_nonneg : ∀ j, HasNonnegCoeffs (q j))
    (hq_ne : ∀ j, q j ≠ 0)
    (hq_splits : ∀ j, (q j).Splits)
    (hq_deg : ∀ j, (q j).natDegree = (j + 1) / 2)
    (hq_interl : ∀ j, StrictInterl (q j) (q (j + 1)))
    {n : ℕ} (hn : 1 ≤ n) :
    StrictInterl (fPolynomial n (q n)) (fPolynomial (n + 1) (q (n + 1))) := by
  let m := (n + 2) / 2
  have hqn_deg : (q n).natDegree ≤ m := by
    rw [hq_deg]
    dsimp [m]
    grind
  have hqnext_deg : (q (n + 1)).natDegree ≤ m := by
    rw [hq_deg]
  have hmax : m = max (q n).natDegree (q (n + 1)).natDegree := by
    rw [hq_deg, hq_deg]
    dsimp [m]
    grind
  have hmin := strictInterl_fPolynomial_of_strictInterl_of_hasNonnegCoeffs_of_minimal
    (d := m) (u := q n) (v := q (n + 1)) hmax (hq_interl n)
      (hq_nonneg n) (hq_nonneg (n + 1))
  have hu := isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hqn_deg
    (hq_ne n) (hq_splits n) (hq_nonneg n)
  have hv := isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hqnext_deg
    (hq_ne (n + 1)) (hq_splits (n + 1)) (hq_nonneg (n + 1))
  have hu_deg := fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hqn_deg
    (hq_nonneg n) (hq_ne n)
  have hv_deg := fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hqnext_deg
    (hq_nonneg (n + 1)) (hq_ne (n + 1))
  have huv := StrictInterl.of_mul_X_sub_C_right_of_roots_ge
    (hf := hu) (hg := hv) (by rw [hu_deg, hv_deg])
    (fPolynomial_roots_ge_neg_one hqn_deg (hq_ne n) (hq_splits n) (hq_nonneg n))
    (fPolynomial_roots_ge_neg_one hqnext_deg (hq_ne (n + 1)) (hq_splits (n + 1))
      (hq_nonneg (n + 1))) hmin
  exact StrictInterl.fPolynomial_pad_of_mul_X_add_one hqn_deg hqnext_deg
    (by dsimp [m]; grind) (by simpa [sub_eq_add_neg] using huv)

end RealRooted

namespace RealRooted
/-- Transfers consecutive strict interlacing through the `f`-polynomial
transform when the auxiliary degree is `j / 2`.  The hypothesis `1 ≤ n`
is not needed: the floor box fits inside row `n` even at `n = 0`. -/
theorem StrictInterl.fPolynomial_sequence_floor
    (q : ℕ → ℝ[X])
    (hq_nonneg : ∀ j, HasNonnegCoeffs (q j))
    (hq_ne : ∀ j, q j ≠ 0)
    (hq_splits : ∀ j, (q j).Splits)
    (hq_deg : ∀ j, (q j).natDegree = j / 2)
    (hq_interl : ∀ j, StrictInterl (q j) (q (j + 1)))
    {n : ℕ} :
    StrictInterl (fPolynomial n (q n))
      (fPolynomial (n + 1) (q (n + 1))) := by
  let m := (n + 1) / 2
  have hqn_deg : (q n).natDegree ≤ m := by
    rw [hq_deg]
    dsimp [m]
    grind
  have hqnext_deg : (q (n + 1)).natDegree ≤ m := by
    rw [hq_deg]
  have hmax : m = max (q n).natDegree (q (n + 1)).natDegree := by
    rw [hq_deg, hq_deg]
    dsimp [m]
    grind
  have hmin := strictInterl_fPolynomial_of_strictInterl_of_hasNonnegCoeffs_of_minimal
    (d := m) (u := q n) (v := q (n + 1)) hmax (hq_interl n)
      (hq_nonneg n) (hq_nonneg (n + 1))
  have hu := isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hqn_deg
    (hq_ne n) (hq_splits n) (hq_nonneg n)
  have hv := isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hqnext_deg
    (hq_ne (n + 1)) (hq_splits (n + 1)) (hq_nonneg (n + 1))
  have hu_deg := fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hqn_deg
    (hq_nonneg n) (hq_ne n)
  have hv_deg := fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hqnext_deg
    (hq_nonneg (n + 1)) (hq_ne (n + 1))
  have huv := StrictInterl.of_mul_X_sub_C_right_of_roots_ge
    (hf := hu) (hg := hv) (by rw [hu_deg, hv_deg])
    (fPolynomial_roots_ge_neg_one hqn_deg (hq_ne n) (hq_splits n)
      (hq_nonneg n))
    (fPolynomial_roots_ge_neg_one hqnext_deg (hq_ne (n + 1))
      (hq_splits (n + 1)) (hq_nonneg (n + 1))) hmin
  exact StrictInterl.fPolynomial_pad_of_mul_X_add_one hqn_deg hqnext_deg
    (by dsimp [m]; grind) (by simpa [sub_eq_add_neg] using huv)
/-- Transfers consecutive strict interlacing through the `f`-polynomial
transform when the auxiliary degrees are `j - 1`. -/
theorem StrictInterl.fPolynomial_sequence_pred
    (q : ℕ → ℝ[X])
    (hq_nonneg : ∀ j, HasNonnegCoeffs (q j))
    (hq_ne : ∀ j, q j ≠ 0)
    (hq_splits : ∀ j, (q j).Splits)
    (hq_deg : ∀ j, (q j).natDegree = j - 1)
    (hq_interl : ∀ j, StrictInterl (q j) (q (j + 1)))
    {n : ℕ} :
    StrictInterl (fPolynomial n (q n))
      (fPolynomial (n + 1) (q (n + 1))) := by
  have hqn_deg : (q n).natDegree ≤ n := by rw [hq_deg]; grind
  have hqnext_deg : (q (n + 1)).natDegree ≤ n := by rw [hq_deg]; grind
  have hmax : n = max (q n).natDegree (q (n + 1)).natDegree := by
    rw [hq_deg, hq_deg]
    grind
  have hmin := strictInterl_fPolynomial_of_strictInterl_of_hasNonnegCoeffs_of_minimal
    (d := n) (u := q n) (v := q (n + 1)) hmax (hq_interl n)
      (hq_nonneg n) (hq_nonneg (n + 1))
  have hu := isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hqn_deg
    (hq_ne n) (hq_splits n) (hq_nonneg n)
  have hv := isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs hqnext_deg
    (hq_ne (n + 1)) (hq_splits (n + 1)) (hq_nonneg (n + 1))
  have hu_deg := fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hqn_deg
    (hq_nonneg n) (hq_ne n)
  have hv_deg := fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hqnext_deg
    (hq_nonneg (n + 1)) (hq_ne (n + 1))
  have huv := StrictInterl.of_mul_X_sub_C_right_of_roots_ge
    (hf := hu) (hg := hv) (by rw [hu_deg, hv_deg])
    (fPolynomial_roots_ge_neg_one hqn_deg (hq_ne n) (hq_splits n)
      (hq_nonneg n))
    (fPolynomial_roots_ge_neg_one hqnext_deg (hq_ne (n + 1))
      (hq_splits (n + 1)) (hq_nonneg (n + 1))) hmin
  exact StrictInterl.fPolynomial_pad_of_mul_X_add_one hqn_deg hqnext_deg
    le_rfl (by simpa [sub_eq_add_neg] using huv)

end RealRooted
