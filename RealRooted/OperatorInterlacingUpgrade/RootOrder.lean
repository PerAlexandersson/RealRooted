import RealRooted.MaWang.Strong
import RealRooted.OrderedRoots
import RealRooted.ObreschkoffConverse.Converse
import RealRooted.ObreschkoffConverse.Forward
import RealRooted.AllCombo
import RealRooted.OperatorInterlacingUpgrade
import RealRooted.FiniteFreeRootCount

/-!
# Root-order preservation for monomial-chain operators

Let `T` be a linear operator satisfying the hypotheses of the monomial-chain interlacing
upgrade (`RealRooted.Challenges.MonomialChainOperator.preservesInterlacing`).  This module shows
that moving one nonpositive input root to the right moves every ordered output root weakly to
the right (`rootwiseLE_monomialChain_rootPolynomial_list_set`), and derives componentwise bounds
for inputs whose roots lie in `[-b, -a]` from the extremal inputs `(X + b) ^ D` and `(X + a) ^ D`
(`rootwiseLE_monomialChain_component_bounds`).  The basic step is the deletion-interlacer root
shift `orderedRoot_sub_C_mul_of_interlaces`.

`StrictInterl` uses weak root comparisons, so common and repeated roots are allowed.

Coordinatewise root order does not imply interlacing for arbitrary pairs: see
`not_strictInterl_separated_quadratics`.  The implicit derivative formula for simple output
roots is not formalized here.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The monomial-chain interlacing upgrade: a PF-preserving linear operator whose consecutive
monomial images form an oriented interlacing chain preserves every oriented interlacing pair
with nonnegative coefficients in the degree box. -/
theorem strictInterl_map_of_monomialChain
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ} {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hgdeg : g.natDegree ≤ D)
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits)
    (hmono : ∀ m : ℕ, m + 1 ≤ D →
      StrictInterl (T (X ^ m)) (T (X ^ (m + 1)))) :
    StrictInterl (T f) (T g) :=
  strictInterl_map_of_pfShift hfg hf hg hgdeg hTnn hTrr
    (preservesPFShiftInterlacingOnDegree_of_monomials hTnn hTrr hmono)

/-- Subtracting a nonnegative deletion interlacer moves every ordered root
weakly to the right. -/
theorem orderedRoot_sub_C_mul_of_interlaces
    {f g : ℝ[X]} (hgf : Interlaces g f)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {c : ℝ} (hc : 0 ≤ c) :
    ∀ i : Fin f.natDegree,
      orderedRoot f f.natDegree i ≤
        orderedRoot (f - C c * g) f.natDegree i := by
  let q : ℝ[X] := f - C c * g
  have hdeg : f.natDegree ≤ f.natDegree := le_rfl
  have hqdeg : q.natDegree = f.natDegree := by
    dsimp [q]
    exact natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound hgf hdeg c
  have hq_pos : HasPosLeadingCoeff q := by
    exact hasPosLeadingCoeff_sub_C_mul_of_interlaces_degree_lower_bound
      hgf hdeg hf_pos c
  have hq_ne : q ≠ 0 := hq_pos.ne_zero
  have hall : AllComboRealRooted g f :=
    allComboRealRooted_of_strictInterl hgf.toStrictInterl
  have hq_eq : q = C (-c) * g + C 1 * f := by
    dsimp [q]
    simp only [C_1, one_mul, sub_eq_add_neg]
    rw [add_comm (C (-c) * g) f]
    have hC : C (-c) = -(C c) := by simp
    rw [hC]
    ring
  have hf_eq : f = C 0 * g + C 1 * f := by simp
  have hq_splits : q.Splits := by
    rw [hq_eq]
    exact hall (-c) 1
  have hall_qf : AllComboRealRooted q f :=
    allComboRealRooted_linear_recombination hq_eq hf_eq hall
  have horient : StrictInterl q f ∨ StrictInterl f q :=
    strictInterl_of_allComboRealRooted hq_ne hq_splits hgf.1.1 hgf.1.2
      hall_qf (Or.inr hqdeg)
  have hidx : f.natDegree - 1 = g.natDegree := by
    have h := hgf.2.2.1
    lia
  have hf_degree_pos : 0 < f.natDegree := by
    have h := hgf.2.2.1
    lia
  have hnext : q.nextCoeff = f.nextCoeff - c * g.leadingCoeff := by
    dsimp [q]
    rw [nextCoeff_of_natDegree_pos hf_degree_pos,
      nextCoeff_of_natDegree_pos (hqdeg ▸ hf_degree_pos), hqdeg,
      coeff_sub, coeff_C_mul, hidx, coeff_natDegree]
  have hq_lc : q.leadingCoeff = f.leadingCoeff := by
    dsimp [q]
    apply leadingCoeff_sub_of_degree_lt
    exact degree_lt_degree <|
      (natDegree_C_mul_le c g).trans_lt
        (by
          have h := hgf.2.2.1
          lia)
  have hf_sum := hgf.1.2.sum_roots_eq_neg_nextCoeff_div_leadingCoeff
    (ne_of_gt hf_pos)
  have hq_sum := hq_splits.sum_roots_eq_neg_nextCoeff_div_leadingCoeff
    (ne_of_gt hq_pos)
  have hsum : f.roots.sum ≤ q.roots.sum := by
    rw [hf_sum, hq_sum, hnext, hq_lc]
    rw [div_le_div_iff₀ hf_pos hf_pos]
    have hcg : 0 ≤ c * g.leadingCoeff := mul_nonneg hc (le_of_lt hg_pos)
    have hprod : 0 ≤ c * g.leadingCoeff * f.leadingCoeff :=
      mul_nonneg hcg (le_of_lt hf_pos)
    nlinarith [hprod]
  have hstrict : StrictInterl f q := by
    rcases horient with hqf | hfq
    · exact hqf.of_reverse_of_roots_sum_le hqdeg.symm hsum
    · exact hfq
  intro i
  simpa [q] using hstrict.orderedRoot_le rfl hqdeg i

/-- The local `StrictInterl` convention permits weak comparisons, hence shared
and repeated roots, in the interlacing lists. -/
private theorem strictInterl_linear_root_move {a b : ℝ} (hab : a ≤ b) :
    StrictInterl (X - C a) (X - C b) := by
  simpa [sub_eq_add_neg] using
    (StrictInterl.X_add_C_iff (a := -b) (b := -a)).mpr (by linarith)

/-- Replacing one entry of a real-root multiset by a larger entry gives the
corresponding root-polynomial interlacing relation. -/
theorem strictInterl_rootPolynomial_cons_move (s : Multiset ℝ) {a b : ℝ}
    (hab : a ≤ b) :
    StrictInterl (rootPolynomial (a ::ₘ s)) (rootPolynomial (b ::ₘ s)) := by
  have h := (strictInterl_linear_root_move hab).mul_common_factor
    (rootPolynomial_monic s).ne_zero (rootPolynomial_splits s)
  simpa [rootPolynomial, mul_comm] using h

/-- The preceding one-root move in list/index form. -/
theorem strictInterl_rootPolynomial_list_set
    (r : List ℝ) (i : ℕ) (hi : i < r.length) {b : ℝ} (h : r[i] ≤ b) :
    StrictInterl (rootPolynomial (r : Multiset ℝ))
      (rootPolynomial ((r.set i b : List ℝ) : Multiset ℝ)) := by
  induction r generalizing i with
  | nil => simp at hi
  | cons a r ih =>
      cases i with
      | zero =>
        have hab : a ≤ b := by simpa using h
        simpa [rootPolynomial] using strictInterl_rootPolynomial_cons_move r hab
      | succ j =>
        have hj : j < r.length := by simpa using hi
        have htail : r[j] ≤ b := by simpa using h
        have hih := ih j hj htail
        have hlinear := isRealRooted_of_degree_one
            (Polynomial.natDegree_X_sub_C a)
        have hcommon := hih.mul_common_factor
          (d := X - C a) hlinear.1 hlinear.2
        simpa [rootPolynomial, mul_comm] using hcommon

/-- A root polynomial with only nonpositive roots has nonnegative coefficients. -/
theorem hasNonnegCoeffs_rootPolynomial_of_nonpos
    (s : Multiset ℝ) (hs : ∀ r ∈ s, r ≤ 0) :
    HasNonnegCoeffs (rootPolynomial s) := by
  induction s using Multiset.induction_on with
  | empty =>
      simpa [rootPolynomial] using (hasNonnegCoeffs_one :
        HasNonnegCoeffs (1 : ℝ[X]))
  | @cons a s ih =>
      rw [rootPolynomial, Multiset.map_cons, Multiset.prod_cons]
      apply (hasNonnegCoeffs_X_sub_C (hs a (Multiset.mem_cons_self a s))).mul
      apply ih
      intro r hr
      exact hs r (Multiset.mem_cons_of_mem hr)

private theorem rootwiseLE_map_rootPolynomial_of_forall₂
    {T : ℝ[X] → ℝ[X]} {D : ℕ}
    (hTdegree : ∀ {p : ℝ[X]}, p.natDegree = D → (T p).natDegree = D)
    (hTpres : ∀ {f g : ℝ[X]}, f.natDegree = D → g.natDegree = D →
      StrictInterl f g → StrictInterl (T f) (T g))
    {xs ys : List ℝ} (hxy : List.Forall₂ (· ≤ ·) xs ys)
    (fixed : Multiset ℝ)
    (htotal : xs.length + fixed.card = D) :
    RootwiseLE
      (T (rootPolynomial ((xs : Multiset ℝ) + fixed)))
      (T (rootPolynomial ((ys : Multiset ℝ) + fixed))) := by
  induction hxy generalizing fixed with
  | nil => exact RootwiseLE.refl _
  | cons hxy htail ih =>
      rename_i u v as bs
      let s : Multiset ℝ := (as : Multiset ℝ) + fixed
      have hdegx : (rootPolynomial (u ::ₘ s)).natDegree = D := by
        rw [natDegree_rootPolynomial]
        simpa [s, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
      have hdegy : (rootPolynomial (v ::ₘ s)).natDegree = D := by
        rw [natDegree_rootPolynomial]
        simpa [s, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
      have hstrict :
          StrictInterl (rootPolynomial (u ::ₘ s)) (rootPolynomial (v ::ₘ s)) :=
        strictInterl_rootPolynomial_cons_move s hxy
      have hTstrict := hTpres hdegx hdegy hstrict
      have hstep :
          RootwiseLE (T (rootPolynomial (u ::ₘ s)))
            (T (rootPolynomial (v ::ₘ s))) :=
        RootwiseLE.of_strictInterl_sameDegree hTstrict
          ((hTdegree hdegx).trans (hTdegree hdegy).symm)
      have htotal' : as.length + (v ::ₘ fixed).card = D := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
      have hrec := ih (fixed := v ::ₘ fixed) htotal'
      have hx : (↑(u :: as) : Multiset ℝ) + fixed = u ::ₘ s := by
        change (u ::ₘ (↑as : Multiset ℝ)) + fixed =
          u ::ₘ ((↑as : Multiset ℝ) + fixed)
        exact Multiset.cons_add u (↑as : Multiset ℝ) fixed
      have hy : (↑(v :: bs) : Multiset ℝ) + fixed =
          (↑bs : Multiset ℝ) + (v ::ₘ fixed) := by
        change (v ::ₘ (↑bs : Multiset ℝ)) + fixed =
          (↑bs : Multiset ℝ) + (v ::ₘ fixed)
        ext z
        by_cases hzy : z = v
        · simp [Multiset.count_add, hzy, add_comm, add_left_comm, add_assoc]
        · simp [Multiset.count_add, hzy, Ne.symm hzy, add_comm]
      rw [hx, hy]
      apply hstep.trans
      simpa [s, add_comm, add_left_comm, add_assoc] using hrec

private theorem rootwiseLE_monomial_forall₂
    {T : ℝ[X] → ℝ[X]} {D : ℕ}
    (hTdegree : ∀ {p : ℝ[X]}, p.natDegree = D → (T p).natDegree = D)
    (hTpres : ∀ {f g : ℝ[X]}, f.natDegree = D → g.natDegree = D →
      HasNonnegCoeffs f → HasNonnegCoeffs g → StrictInterl f g →
      StrictInterl (T f) (T g))
    {xs ys : List ℝ} (hxy : List.Forall₂ (· ≤ ·) xs ys)
    (fixed : Multiset ℝ) (hfixed : ∀ z ∈ fixed, z ≤ 0)
    (htotal : xs.length + fixed.card = D)
    (hxs : ∀ x ∈ xs, x ≤ 0) (hys : ∀ y ∈ ys, y ≤ 0) :
    RootwiseLE
      (T (rootPolynomial ((xs : Multiset ℝ) + fixed)))
      (T (rootPolynomial ((ys : Multiset ℝ) + fixed))) := by
  revert fixed hfixed htotal hxs hys
  induction hxy with
  | nil =>
      intro fixed hfixed htotal hxs hys
      exact RootwiseLE.refl _
  | cons hxy htail ih =>
      rename_i u v as bs
      intro fixed hfixed htotal hxs hys
      let s : Multiset ℝ := (as : Multiset ℝ) + fixed
      have has : ∀ z ∈ as, z ≤ 0 := by
        intro z hz
        exact hxs z (List.mem_cons_of_mem u hz)
      have hbs : ∀ z ∈ bs, z ≤ 0 := by
        intro z hz
        exact hys z (List.mem_cons_of_mem v hz)
      have hs : ∀ z ∈ s, z ≤ 0 := by
        intro z hz
        rcases Multiset.mem_add.mp hz with hz | hz
        · exact has z (Multiset.mem_coe.mp hz)
        · exact hfixed z hz
      have hu : ∀ z ∈ u ::ₘ s, z ≤ 0 := by
        intro z hz
        simp only [Multiset.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hxs z (by simp)
        · exact hs z hz
      have hv : ∀ z ∈ v ::ₘ s, z ≤ 0 := by
        intro z hz
        simp only [Multiset.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hys z (by simp)
        · exact hs z hz
      have hdeg_u : (rootPolynomial (u ::ₘ s)).natDegree = D := by
        rw [natDegree_rootPolynomial]
        simpa [s, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
      have hdeg_v : (rootPolynomial (v ::ₘ s)).natDegree = D := by
        rw [natDegree_rootPolynomial]
        simpa [s, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
      have hstep := hTpres hdeg_u hdeg_v
        (hasNonnegCoeffs_rootPolynomial_of_nonpos _ hu)
        (hasNonnegCoeffs_rootPolynomial_of_nonpos _ hv)
        (strictInterl_rootPolynomial_cons_move s hxy)
      have hstep' : RootwiseLE
          (T (rootPolynomial (u ::ₘ s)))
          (T (rootPolynomial (v ::ₘ s))) :=
        RootwiseLE.of_strictInterl_sameDegree hstep
          ((hTdegree hdeg_u).trans (hTdegree hdeg_v).symm)
      have hfixed' : ∀ z ∈ v ::ₘ fixed, z ≤ 0 := by
        intro z hz
        simp only [Multiset.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hys z (by simp)
        · exact hfixed z hz
      have htotal' : as.length + (v ::ₘ fixed).card = D := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
      have htail' := ih (v ::ₘ fixed) hfixed' htotal' has hbs
      have hu_eq : (↑(u :: as) : Multiset ℝ) + fixed = u ::ₘ s := by
        change (u ::ₘ (↑as : Multiset ℝ)) + fixed =
          u ::ₘ ((↑as : Multiset ℝ) + fixed)
        exact Multiset.cons_add u (↑as : Multiset ℝ) fixed
      have hv_eq : (↑(v :: bs) : Multiset ℝ) + fixed =
          (↑bs : Multiset ℝ) + (v ::ₘ fixed) := by
        change (v ::ₘ (↑bs : Multiset ℝ)) + fixed =
          (↑bs : Multiset ℝ) + (v ::ₘ fixed)
        ext z
        by_cases hz : z = v
        · simp [Multiset.count_add, hz, add_comm, add_left_comm, add_assoc]
        · simp [Multiset.count_add, hz, Ne.symm hz, add_comm]
      rw [hu_eq, hv_eq]
      apply hstep'.trans
      simpa [s, add_comm, add_left_comm, add_assoc] using htail'

/-- A monomial-chain operator preserves ordered output roots for an indexed
one-root move; nonnegative coefficients are derived from nonpositive roots. -/
theorem rootwiseLE_monomialChain_rootPolynomial_list_set
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ} (r : List ℝ) (i : ℕ)
    (hi : i < r.length) {b : ℝ} (hmove : r[i] ≤ b)
    (hr : ∀ x ∈ (r : Multiset ℝ), x ≤ 0)
    (hr_set : ∀ x ∈ ((r.set i b : List ℝ) : Multiset ℝ), x ≤ 0)
    (hTdegree : ∀ {p : ℝ[X]}, p.natDegree = D → (T p).natDegree = D)
    (hTnn : ∀ ⦃p : ℝ[X]⦄, HasNonnegCoeffs p → HasNonnegCoeffs (T p))
    (hTrr : ∀ ⦃p : ℝ[X]⦄, IsPFPolynomial p → p ≠ 0 →
      p.natDegree ≤ D → T p ≠ 0 ∧ (T p).Splits)
    (hmono : ∀ m : ℕ, m + 1 ≤ D →
      StrictInterl (T (X ^ m)) (T (X ^ (m + 1))))
    (hD : r.length = D) :
    RootwiseLE
      (T (rootPolynomial (r : Multiset ℝ)))
      (T (rootPolynomial ((r.set i b : List ℝ) : Multiset ℝ))) := by
  have hTpres : ∀ {f g : ℝ[X]}, f.natDegree = D → g.natDegree = D →
      HasNonnegCoeffs f → HasNonnegCoeffs g → StrictInterl f g →
      StrictInterl (T f) (T g) := by
    intro f g hfdeg hgdeg hf hg hfg
    exact strictInterl_map_of_monomialChain hfg hf hg
      (by rw [hgdeg]) hTnn hTrr hmono
  have hdeg_r : (rootPolynomial (r : Multiset ℝ)).natDegree = D := by
    rw [natDegree_rootPolynomial]
    simp [hD]
  have hset_length : (r.set i b : List ℝ).length = D := by
    simp [hD]
  have hdeg_set :
      (rootPolynomial ((r.set i b : List ℝ) : Multiset ℝ)).natDegree = D := by
    rw [natDegree_rootPolynomial]
    simp [hset_length]
  have hstrict := strictInterl_rootPolynomial_list_set r i hi hmove
  have hTstrict := hTpres hdeg_r hdeg_set
    (hasNonnegCoeffs_rootPolynomial_of_nonpos _ hr)
    (hasNonnegCoeffs_rootPolynomial_of_nonpos _ hr_set) hstrict
  exact RootwiseLE.of_strictInterl_sameDegree hTstrict
    ((hTdegree hdeg_r).trans (hTdegree hdeg_set).symm)

private theorem rootPolynomial_replicate_neg
    (c : ℝ) (n : ℕ) :
    rootPolynomial ((List.replicate n (-c) : List ℝ) : Multiset ℝ) =
      (X + C c) ^ n := by
  induction n with
  | zero => simp [rootPolynomial]
  | succ n ih =>
      change (X - C (-c)) *
          rootPolynomial ((List.replicate n (-c) : List ℝ) : Multiset ℝ) =
        (X + C c) ^ (n + 1)
      rw [ih]
      simp only [sub_eq_add_neg]
      have hC : C (-c) = -(C c) := by simp
      rw [hC]
      ring

private theorem rootwiseLE_bounds_from_preserver
    {T : ℝ[X] → ℝ[X]} {D : ℕ} {p : ℝ[X]} {a b : ℝ}
    (hT : PreservesFullDegreeRootMoves D T)
    (hmonic : p.Monic) (hsplits : p.Splits) (hdeg : p.natDegree = D)
    (hlo : ∀ r ∈ p.roots, -b ≤ r)
    (hhi : ∀ r ∈ p.roots, r ≤ -a) :
    RootwiseLE (T ((X + C b) ^ D)) (T p) ∧
      RootwiseLE (T p) (T ((X + C a) ^ D)) := by
  let ps := p.roots.sort (· ≤ ·)
  have hps_len : ps.length = D := by
    simp [ps, card_roots_of_splits hsplits, hdeg]
  have hps_sort : (↑ps : Multiset ℝ) = p.roots :=
    Multiset.sort_eq p.roots (· ≤ ·)
  have hlo_list : List.Forall₂ (· ≤ ·) (List.replicate D (-b)) ps := by
    apply List.forall₂_of_length_eq_of_get
    · simp [hps_len]
    intro i hi_left hi_right
    have hroot : ps[i] ∈ p.roots := by
      rw [← hps_sort]
      exact Multiset.mem_coe.mpr (List.get_mem _ _)
    simpa using hlo _ hroot
  have hhi_list : List.Forall₂ (· ≤ ·) ps (List.replicate D (-a)) := by
    apply List.forall₂_of_length_eq_of_get
    · simp [hps_len]
    intro i hi_left hi_right
    have hroot : ps[i] ∈ p.roots := by
      rw [← hps_sort]
      exact Multiset.mem_coe.mpr (List.get_mem _ _)
    simpa using hhi _ hroot
  have hPpoly : rootPolynomial (ps : Multiset ℝ) = p := by
    rw [hps_sort]
    simpa [rootPolynomial] using (hsplits.eq_prod_roots_of_monic hmonic).symm
  have hlo := rootwiseLE_map_rootPolynomial_of_forall₂
    hT.1 hT.2 hlo_list 0 (by simp)
  have hhi' := rootwiseLE_map_rootPolynomial_of_forall₂
    hT.1 hT.2 hhi_list 0 (by simp [hps_len])
  simp only [Multiset.add_zero] at hlo hhi'
  rw [rootPolynomial_replicate_neg b D, hPpoly] at hlo
  rw [hPpoly, rootPolynomial_replicate_neg a D] at hhi'
  exact ⟨hlo, hhi'⟩

/-- Endpoint bounds for any degree-preserving operator that preserves every
strictly interlacing pair. -/
theorem PreservesFullDegreeRootMoves.rootwiseLE_bounds
    {T : ℝ[X] → ℝ[X]} {D : ℕ} {p : ℝ[X]} {a b : ℝ}
    (hT : PreservesFullDegreeRootMoves D T)
    (hmonic : p.Monic) (hsplits : p.Splits) (hdeg : p.natDegree = D)
    (hlo : ∀ r ∈ p.roots, -b ≤ r)
    (hhi : ∀ r ∈ p.roots, r ≤ -a) :
    RootwiseLE (T ((X + C b) ^ D)) (T p) ∧
      RootwiseLE (T p) (T ((X + C a) ^ D)) :=
  rootwiseLE_bounds_from_preserver hT hmonic hsplits hdeg hlo hhi

/-- Endpoint bounds for a monomial-chain operator on a nonpositive root box.
The lower endpoint assumption `0 ≤ a` supplies nonnegative coefficients at every
intermediate root list. -/
theorem rootwiseLE_monomialChain_component_bounds
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {D : ℕ} {p : ℝ[X]} {a b : ℝ}
    (hmonic : p.Monic) (hsplits : p.Splits) (hdeg : p.natDegree = D)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hlo : ∀ r ∈ p.roots, -b ≤ r)
    (hhi : ∀ r ∈ p.roots, r ≤ -a)
    (hTdegree : ∀ {q : ℝ[X]}, q.natDegree = D → (T q).natDegree = D)
    (hTnn : ∀ ⦃q : ℝ[X]⦄, HasNonnegCoeffs q → HasNonnegCoeffs (T q))
    (hTrr : ∀ ⦃q : ℝ[X]⦄, IsPFPolynomial q → q ≠ 0 →
      q.natDegree ≤ D → T q ≠ 0 ∧ (T q).Splits)
    (hmono : ∀ m : ℕ, m + 1 ≤ D →
      StrictInterl (T (X ^ m)) (T (X ^ (m + 1)))) :
    RootwiseLE (T ((X + C b) ^ D)) (T p) ∧
      RootwiseLE (T p) (T ((X + C a) ^ D)) := by
  let ps := p.roots.sort (· ≤ ·)
  have hps_len : ps.length = D := by
    simp [ps, card_roots_of_splits hsplits, hdeg]
  have hps_sort : (↑ps : Multiset ℝ) = p.roots :=
    Multiset.sort_eq p.roots (· ≤ ·)
  have hlo_list : List.Forall₂ (· ≤ ·) (List.replicate D (-b)) ps := by
    apply List.forall₂_of_length_eq_of_get
    · simp [hps_len]
    intro i hi_left hi_right
    have hroot : ps[i] ∈ p.roots := by
      rw [← hps_sort]
      exact Multiset.mem_coe.mpr (List.get_mem _ _)
    simpa using hlo _ hroot
  have hhi_list : List.Forall₂ (· ≤ ·) ps (List.replicate D (-a)) := by
    apply List.forall₂_of_length_eq_of_get
    · simp [hps_len]
    intro i hi_left hi_right
    have hroot : ps[i] ∈ p.roots := by
      rw [← hps_sort]
      exact Multiset.mem_coe.mpr (List.get_mem _ _)
    simpa using hhi _ hroot
  have hps_nonpos : ∀ r ∈ ps, r ≤ 0 := by
    intro r hr
    have hroot : r ∈ p.roots := by
      rw [← hps_sort]
      exact Multiset.mem_coe.mpr hr
    exact (hhi r hroot).trans (by linarith)
  have hlo_nonpos : ∀ r ∈ List.replicate D (-b), r ≤ 0 := by
    intro r hr
    have hmem : ¬ D = 0 ∧ r = -b := by simpa using hr
    have hr_eq : r = -b := hmem.2
    rw [hr_eq]
    linarith
  have hhi_nonpos : ∀ r ∈ List.replicate D (-a), r ≤ 0 := by
    intro r hr
    have hmem : ¬ D = 0 ∧ r = -a := by simpa using hr
    have hr_eq : r = -a := hmem.2
    rw [hr_eq]
    exact neg_nonpos.mpr ha
  have hTpres : ∀ {f g : ℝ[X]}, f.natDegree = D → g.natDegree = D →
      HasNonnegCoeffs f → HasNonnegCoeffs g → StrictInterl f g →
      StrictInterl (T f) (T g) := by
    intro f g hfdeg hgdeg hf hg hfg
    exact strictInterl_map_of_monomialChain hfg hf hg
      (by rw [hgdeg]) hTnn hTrr hmono
  have hlo := rootwiseLE_monomial_forall₂ hTdegree hTpres hlo_list 0
    (by simp) (by simp) hlo_nonpos hps_nonpos
  have hhi' := rootwiseLE_monomial_forall₂ hTdegree hTpres hhi_list 0
    (by simp) (by simp [hps_len]) hps_nonpos hhi_nonpos
  have hPpoly : rootPolynomial (ps : Multiset ℝ) = p := by
    rw [hps_sort]
    simpa [rootPolynomial] using (hsplits.eq_prod_roots_of_monic hmonic).symm
  simp only [Multiset.add_zero] at hlo hhi'
  rw [rootPolynomial_replicate_neg b D, hPpoly] at hlo
  rw [hPpoly, rootPolynomial_replicate_neg a D] at hhi'
  exact ⟨hlo, hhi'⟩

private lemma sorted_pair_eq {a b : ℝ} (hab : a < b) {l : List ℝ}
    (hsorted : l.Pairwise (· ≤ ·)) (hcoe : (↑l : Multiset ℝ) = {a, b}) :
    l = [a, b] := by
  have hlen : l.length = 2 := by
    have h := congrArg Multiset.card hcoe
    simpa using h
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen
  have hxy : x ≤ y := (List.pairwise_cons.mp hsorted).1 y (by simp)
  have hne : a ≠ b := ne_of_lt hab
  have hxab : x = a ∨ x = b := by
    have hx : x ∈ ({a, b} : Multiset ℝ) := by
      rw [← hcoe]
      simp
    simp_all
  have hyab : y = a ∨ y = b := by
    have hy : y ∈ ({a, b} : Multiset ℝ) := by
      rw [← hcoe]
      simp
    simp_all
  rcases hxab with rfl | rfl <;> rcases hyab with rfl | rfl
  · exfalso
    have hcount := congrArg (Multiset.count b) hcoe
    simp [Ne.symm hne] at hcount
  · simp
  · grind
  · exfalso
    have hcount := congrArg (Multiset.count a) hcoe
    simp [hne] at hcount

/-- The roots `(0,1)` and `(3,4)` are coordinatewise ordered but do not
interlace, witnessing the warning needed for arbitrary output pairs. -/
theorem not_strictInterl_separated_quadratics :
    ¬ StrictInterl (X * (X - C 1)) ((X - C 3) * (X - C 4)) := by
  let f : ℝ[X] := X * (X - C 1)
  let g : ℝ[X] := (X - C 3) * (X - C 4)
  have hf : f = rootPolynomial ({0, 1} : Multiset ℝ) := by
    dsimp [f, rootPolynomial]
    simp [sub_eq_add_neg]
  have hg : g = rootPolynomial ({3, 4} : Multiset ℝ) := by
    dsimp [g, rootPolynomial]
    simp [sub_eq_add_neg]
  change ¬ StrictInterl f g
  rw [hf, hg]
  intro h
  rcases h with ⟨-, -, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_eq' : (↑ss : Multiset ℝ) = {0, 1} := by simpa using hss_eq
  have hrs_eq' : (↑rs : Multiset ℝ) = {3, 4} := by simpa using hrs_eq
  have hsseq : ss = [0, 1] :=
    sorted_pair_eq (by norm_num) hss hss_eq'
  have hrseq : rs = [3, 4] :=
    sorted_pair_eq (by norm_num) hrs hrs_eq'
  subst hsseq
  subst hrseq
  rcases hshape with ⟨hlen, _⟩ | ⟨_, halt⟩
  · simp_all
  · simp only [ListAlternates, ListInterlaces] at halt
    simp_all

end RealRooted
