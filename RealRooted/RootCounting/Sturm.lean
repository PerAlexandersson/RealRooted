import RealRooted.Mathlib.Algebra.Polynomial.Sturm
import RealRooted.Mathlib.LinearAlgebra.Matrix.SignVariationTopology
import RealRooted.RootCountJump
import RealRooted.SimpleRoots
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Sturm root counting

The sign variation of the signed remainder sequence of `p` and `p'` drops by
one at each distinct real root of `p` and is locally constant elsewhere.  This
gives the exact open-interval root count.  The public arbitrary-polynomial API
applies the theorem to the radical, which removes repeated factors without
changing the set of roots.
-/

open Filter Polynomial Set UniqueFactorizationMonoid
open scoped Topology

noncomputable section

namespace RealRooted

/-- The classical Sturm sequence of a real polynomial. -/
def sturmSequence (p : ℝ[X]) : List ℝ[X] :=
  Polynomial.signedRemainderSequence p p.derivative

/-- The values of the Sturm sequence at a real point. -/
def sturmValues (p : ℝ[X]) (x : ℝ) : List ℝ :=
  (sturmSequence p).map fun q ↦ q.eval x

/-- The zero-omitting sign variation of a Sturm sequence at a point. -/
def sturmVariations (p : ℝ[X]) (x : ℝ) : ℕ :=
  (sturmValues p x).signVariations

@[simp]
theorem length_sturmValues (p : ℝ[X]) (x : ℝ) :
    (sturmValues p x).length = (sturmSequence p).length := by
  simp [sturmValues]

theorem HasSimpleRoots.noCommonRoot_derivative {p : ℝ[X]}
    (hp : HasSimpleRoots p) :
    Polynomial.NoCommonRoot p p.derivative := by
  intro x hx
  exact hp.eval_derivative_ne_zero hx.1 (by simpa [Polynomial.IsRoot] using hx.2)

private theorem eventually_variations_pair_eq
    {p q : ℝ[X]} (hcop : Polynomial.NoCommonRoot p q)
    {x : ℝ} (hpx : p.eval x ≠ 0) :
    ∀ᶠ y in 𝓝 x,
      ((Polynomial.signedRemainderSequence p q).map fun r ↦ r.eval y).signVariations =
        ((Polynomial.signedRemainderSequence p q).map fun r ↦ r.eval x).signVariations := by
  let l := Polynomial.signedRemainderSequence p q
  let vx : List ℝ := l.map fun r ↦ r.eval x
  let vy : ℝ → List ℝ := fun y ↦ l.map fun r ↦ r.eval y
  by_cases hq : q = 0
  · subst q
    simp [Polynomial.signedRemainderSequence_zero_right]
  · have htwo : 2 ≤ vx.length := by
      have hlen' : 2 ≤ (Polynomial.signedRemainderSequence p q).length := by
        have := Polynomial.one_lt_length_signedRemainderSequence (p := p) hq
        lia
      simpa [vx, l] using hlen'
    have hfirst : vx[0]'(by lia) ≠ 0 := by
      simp [vx, l, Polynomial.signedRemainderSequence_ne_zero_right p hq, hpx]
    have hlast : vx[vx.length - 1]'(by lia) ≠ 0 := by
      have hlpos : 0 < l.length := by
        simp [l, Polynomial.signedRemainderSequence_length_pos]
      have hlidx : l.length - 1 < l.length := by lia
      have hlastl : (l[l.length - 1]'hlidx).eval x ≠ 0 := by
        rw [List.getElem_length_sub_one_eq_getLast hlidx]
        exact Polynomial.eval_getLast_signedRemainderSequence_ne_zero hcop x
      simpa only [vx, List.length_map, List.getElem_map] using hlastl
    have hrem :=
      Polynomial.isSignedRemainderChain_signedRemainderSequence p q
    have hchain :=
      Polynomial.isChain_noCommonRoot_signedRemainderSequence hcop
    have hnodal : ∀ i (hi : i + 2 < vx.length), vx[i + 1] = 0 →
        vx[i] * vx[i + 2] < 0 := by
      intro i hi hz
      simpa [vx, l] using
        Polynomial.eval_neighbors_mul_neg_of_isSignedRemainderChain_of_linearOrder
          hrem hchain x i (by simpa [vx, l] using hi)
            (by simpa [vx, l] using hz)
    let f : ℝ → Fin l.length → ℝ := fun y i ↦ l[i].eval y
    have hf : Tendsto f (nhds x) (nhds (f x)) := by
      rw [tendsto_pi_nhds]
      intro i
      exact l[i].continuousAt
    filter_upwards [Fin.eventually_sign_eq_of_tendsto hf] with y hy
    exact List.signVariations_eq_of_sign_eq_on_nonzero_of_interior_nodal
      (x := vx) (y := vy y) (by simp [vx, vy]) htwo hfirst hlast
      (fun i hi hne ↦ by
        convert hy ⟨i, by simpa [vx, l] using hi⟩
          (by simpa [f, vx, l] using hne) using 1 <;>
          simp [f, vx, vy]) hnodal

private theorem eventually_sturmVariations_eq_of_not_isRoot
    {p : ℝ[X]} (hp : HasSimpleRoots p) {x : ℝ}
    (hx : ¬ p.IsRoot x) :
    ∀ᶠ y in 𝓝 x, sturmVariations p y = sturmVariations p x := by
  simpa [sturmVariations, sturmValues, sturmSequence] using
    eventually_variations_pair_eq hp.noCommonRoot_derivative
      ((Polynomial.not_isRoot_iff_eval_ne_zero p x).mp hx)

private theorem eval_divByMonic_X_sub_C_eq_derivative_of_isRoot
    {p : ℝ[X]} {x : ℝ} (_hx : p.IsRoot x) :
    (p /ₘ (X - C x)).eval x = p.derivative.eval x := by
  have h := congrArg (fun q : ℝ[X] ↦ q.eval x)
    (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative p x)
  simpa using h

private theorem eventually_sturmVariations_root_formula
    {p : ℝ[X]} (hp : HasSimpleRoots p) {x : ℝ}
    (hx : p.IsRoot x) :
    ∀ᶠ y in 𝓝 x,
      sturmVariations p y =
        sturmVariations p x + if y < x then 1 else 0 := by
  have hderx : p.derivative.eval x ≠ 0 := hp.eval_derivative_ne_zero hx
  have hder : p.derivative ≠ 0 := fun h ↦ hderx (by simp [h])
  let r := -(p % p.derivative)
  let tail := Polynomial.signedRemainderSequence p.derivative r
  obtain ⟨rest, hrest⟩ :=
    Polynomial.exists_tail_signedRemainderSequence p.derivative r
  have hrest' : tail = p.derivative :: rest := by
    simpa [tail] using hrest
  have hnext := hp.noCommonRoot_derivative.next
  have htail :
      ∀ᶠ y in 𝓝 x,
        (tail.map fun q ↦ q.eval y).signVariations =
          (tail.map fun q ↦ q.eval x).signVariations := by
    simpa [tail, r] using eventually_variations_pair_eq hnext hderx
  let c := p /ₘ (X - C x)
  have hcx : c.eval x = p.derivative.eval x :=
    eval_divByMonic_X_sub_C_eq_derivative_of_isRoot hx
  have hcne : c.eval x ≠ 0 := hcx ▸ hderx
  have hfactor : (X - C x) * c = p :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hx
  let f : ℝ → Fin 2 → ℝ := fun y i ↦
    if i = 0 then c.eval y else p.derivative.eval y
  have hf : Tendsto f (nhds x) (nhds (f x)) := by
    rw [tendsto_pi_nhds]
    intro i
    fin_cases i
    · change Tendsto (fun y ↦ c.eval y) (nhds x) (nhds (c.eval x))
      exact c.continuousAt
    · change Tendsto (fun y ↦ p.derivative.eval y) (nhds x)
        (nhds (p.derivative.eval x))
      exact p.derivative.continuousAt
  filter_upwards [htail, Fin.eventually_sign_eq_of_tendsto hf] with y htail_y hsign
  have hc_y_ne : c.eval y ≠ 0 := by
    intro hzero
    have hs := hsign 0 hcne
    have : SignType.sign (p.derivative.eval x) = 0 := by
      simpa [f, hcx, hzero] using hs.symm
    exact hderx (sign_eq_zero_iff.mp this)
  have hd_y_ne : p.derivative.eval y ≠ 0 := by
    intro hzero
    have hs := hsign 1 hderx
    have : SignType.sign (p.derivative.eval x) = 0 := by
      simpa [f, hzero] using hs.symm
    exact hderx (sign_eq_zero_iff.mp this)
  have hcdsign : SignType.sign (c.eval y) = SignType.sign (p.derivative.eval y) := by
    calc
      SignType.sign (c.eval y) = SignType.sign (c.eval x) := by simpa [f] using hsign 0 hcne
      _ = SignType.sign (p.derivative.eval x) := by rw [hcx]
      _ = SignType.sign (p.derivative.eval y) := by
        symm
        simpa [f] using hsign 1 hderx
  have hpy : p.eval y = (y - x) * c.eval y := by
    rw [← hfactor, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
  have hseq : sturmSequence p = p :: tail := by
    simpa [sturmSequence, tail, r] using
      Polynomial.signedRemainderSequence_ne_zero_right p hder
  have hrootVariation : sturmVariations p x =
      (tail.map fun q ↦ q.eval x).signVariations := by
    simp [sturmVariations, sturmValues, hseq, Polynomial.IsRoot.def.mp hx]
  rw [sturmVariations, sturmValues, hseq, List.map_cons]
  by_cases hyx : y = x
  · subst y
    simp [Polynomial.IsRoot.def.mp hx, hrootVariation]
  · have hpyne : p.eval y ≠ 0 := by
      rw [hpy]
      exact mul_ne_zero (sub_ne_zero.mpr hyx) hc_y_ne
    rw [hrest'] at htail_y hrootVariation ⊢
    simp only [List.map_cons] at htail_y hrootVariation ⊢
    rw [List.signVariations_cons_cons_of_ne_zero _ hpyne hd_y_ne,
      htail_y, ← hrootVariation]
    by_cases hylt : y < x
    · have hsign_ne : SignType.sign (p.eval y) ≠
          SignType.sign (p.derivative.eval y) := by
        have hsne : SignType.sign (p.derivative.eval y) ≠ 0 :=
          sign_ne_zero.mpr hd_y_ne
        rw [hpy, sign_mul, sign_neg (sub_neg.mpr hylt), hcdsign]
        generalize SignType.sign (p.derivative.eval y) = s at hsne ⊢
        fin_cases s <;> simp_all
      simp [hylt, hsign_ne]
    · have hxy : x < y := lt_of_le_of_ne (not_lt.mp hylt) (Ne.symm hyx)
      have hsign_eq : SignType.sign (p.eval y) =
          SignType.sign (p.derivative.eval y) := by
        rw [hpy, sign_mul, sign_pos (sub_pos.mpr hxy), hcdsign]
        simp
      simp [hylt, hsign_eq]

private theorem Multiset.eventually_card_filter_le_eq_of_not_mem
    (s : Multiset ℝ) {x : ℝ} (hx : x ∉ s) :
    ∀ᶠ y in 𝓝 x,
      (s.filter (· ≤ y)).card = (s.filter (· ≤ x)).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have hax : a ≠ x := fun h ↦ hx (by simp [h])
      have hxs : x ∉ s := fun h ↦ hx (by simp [h])
      rcases lt_or_gt_of_ne hax with hax | hxa
      · filter_upwards [ih hxs, Ioi_mem_nhds hax] with y hy hay
        change a < y at hay
        simp [hy, hax.le, hay.le]
      · filter_upwards [ih hxs, Iio_mem_nhds hxa] with y hy hya
        change y < a at hya
        simp [hy, not_le.mpr hxa, not_le.mpr hya]

private theorem Multiset.eventually_card_filter_le_root_formula
    (s : Multiset ℝ) {x : ℝ} (hx : x ∈ s) (hcount : s.count x = 1) :
    ∀ᶠ y in 𝓝 x,
      (s.filter (· ≤ y)).card + (if y < x then 1 else 0) =
        (s.filter (· ≤ x)).card := by
  have hxerase : x ∉ s.erase x := by
    rw [← Multiset.count_eq_zero, Multiset.count_erase_self, hcount]
  filter_upwards [Multiset.eventually_card_filter_le_eq_of_not_mem
    (s.erase x) hxerase] with y hy
  conv_lhs => rw [← Multiset.cons_erase hx]
  conv_rhs => rw [← Multiset.cons_erase hx]
  by_cases hyx : y < x
  · simp [hyx, hy]
  · simp [hyx, not_lt.mp hyx, hy]

private theorem sturmInvariant_isLocallyConstant {p : ℝ[X]}
    (hp : HasSimpleRoots p) :
    IsLocallyConstant fun x ↦
      sturmVariations p x + (p.roots.filter (· ≤ x)).card := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : p.IsRoot x
  · have hxmem : x ∈ p.roots := (Polynomial.mem_roots hp.ne_zero).2 hx
    filter_upwards [eventually_sturmVariations_root_formula hp hx,
      Multiset.eventually_card_filter_le_root_formula p.roots hxmem
        (hp.roots_count_eq_one hx)] with y hv hc
    rw [hv, ← hc]
    lia
  · have hxmem : x ∉ p.roots := by
      simpa [Polynomial.mem_roots hp.ne_zero] using hx
    filter_upwards [eventually_sturmVariations_eq_of_not_isRoot hp hx,
      Multiset.eventually_card_filter_le_eq_of_not_mem p.roots hxmem] with y hv hc
    simp [hv, hc]

/-- Sturm's global invariant: variation plus the number of real roots at or
below the threshold is independent of the threshold. -/
theorem sturmVariations_add_card_roots_filter_le_eq
    {p : ℝ[X]} (hp : HasSimpleRoots p) (a b : ℝ) :
    sturmVariations p a + (p.roots.filter (· ≤ a)).card =
      sturmVariations p b + (p.roots.filter (· ≤ b)).card :=
  (sturmInvariant_isLocallyConstant hp).apply_eq_of_isPreconnected
    isPreconnected_univ (Set.mem_univ a) (Set.mem_univ b)

/-- Sturm's theorem for a polynomial with simple real roots.  Endpoint roots
are excluded, and roots in the open interval are counted exactly. -/
theorem card_roots_filter_Ioo_eq_sturmVariations_sub
    {p : ℝ[X]} (hp : HasSimpleRoots p) {a b : ℝ} (hab : a < b)
    (_ha : ¬ p.IsRoot a) (hb : ¬ p.IsRoot b) :
    (p.roots.filter fun r ↦ a < r ∧ r < b).card =
      sturmVariations p a - sturmVariations p b := by
  have hinv := sturmVariations_add_card_roots_filter_le_eq hp a b
  have hpart := card_filter_Ioo_add_card_filter_ge_eq_card_filter_gt p.roots hab
  have hcard := Multiset.card_filter_le_add_card_filter_gt p.roots a
  have hbmem : b ∉ p.roots := by
    simpa [Polynomial.mem_roots hp.ne_zero] using hb
  have hge : (p.roots.filter (b ≤ ·)).card =
      (p.roots.filter (b < ·)).card := by
    rw [Multiset.filter_ge_eq_filter_gt_of_not_mem p.roots hbmem]
  rw [hge] at hpart
  have hpart' : (p.roots.filter (· ≤ b)).card =
      (p.roots.filter (· ≤ a)).card +
        (p.roots.filter fun r ↦ a < r ∧ r < b).card := by
    have hbcard := Multiset.card_filter_le_add_card_filter_gt p.roots b
    lia
  rw [hpart'] at hinv
  lia

/-! ## Radical normalization -/

/-- The canonical squarefree part used by the public Sturm API. -/
def sturmSquarefreePart (p : ℝ[X]) : ℝ[X] :=
  radical p

@[simp]
theorem sturmSquarefreePart_ne_zero (p : ℝ[X]) :
    sturmSquarefreePart p ≠ 0 := by
  simp [sturmSquarefreePart]

theorem hasSimpleRoots_sturmSquarefreePart (p : ℝ[X]) :
    HasSimpleRoots (sturmSquarefreePart p) := by
  have hsep : (sturmSquarefreePart p).Separable :=
    PerfectField.separable_iff_squarefree.mpr (by
      simpa [sturmSquarefreePart] using squarefree_radical (a := p))
  intro x hx
  have hpos : 0 < (sturmSquarefreePart p).rootMultiplicity x :=
    (Polynomial.rootMultiplicity_pos (sturmSquarefreePart_ne_zero p)).2 hx
  have hle := Polynomial.rootMultiplicity_le_one_of_separable hsep x
  lia

theorem isRoot_sturmSquarefreePart_iff {p : ℝ[X]} (hp : p ≠ 0) (x : ℝ) :
    (sturmSquarefreePart p).IsRoot x ↔ p.IsRoot x := by
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := radical_dvd_self (a := p)
    rw [Polynomial.IsRoot] at hx ⊢
    rw [hq, Polynomial.eval_mul, show (radical p).eval x = 0 by
      simpa [sturmSquarefreePart] using hx, zero_mul]
  · intro hx
    obtain ⟨n, q, hq⟩ := exists_dvd_radical_self_pow hp
    rw [Polynomial.IsRoot] at hx ⊢
    have hpow : (sturmSquarefreePart p).eval x ^ n = 0 := by
      rw [← Polynomial.eval_pow, show sturmSquarefreePart p ^ n = p * q by
        simpa [sturmSquarefreePart] using hq, Polynomial.eval_mul, hx, zero_mul]
    exact eq_zero_of_pow_eq_zero hpow

theorem roots_toFinset_sturmSquarefreePart {p : ℝ[X]} (hp : p ≠ 0) :
    (sturmSquarefreePart p).roots.toFinset = p.roots.toFinset := by
  ext x
  simp only [Multiset.mem_toFinset]
  rw [Polynomial.mem_roots (sturmSquarefreePart_ne_zero p),
    Polynomial.mem_roots hp]
  exact isRoot_sturmSquarefreePart_iff hp x

/-- The number of distinct real roots of `p` in `(a,b)`. -/
def distinctRootCountIoo (p : ℝ[X]) (a b : ℝ) : ℕ :=
  (p.roots.toFinset.filter fun r ↦ a < r ∧ r < b).card

/-- The public Sturm variation applies the signed remainder construction to
the canonical squarefree part. -/
def distinctSturmVariations (p : ℝ[X]) (x : ℝ) : ℕ :=
  sturmVariations (sturmSquarefreePart p) x

/-- Sturm's theorem for an arbitrary nonzero real polynomial, counting
distinct roots in an open interval. -/
theorem distinctRootCountIoo_eq_distinctSturmVariations_sub
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ} (hab : a < b)
    (ha : ¬ p.IsRoot a) (hb : ¬ p.IsRoot b) :
    distinctRootCountIoo p a b =
      distinctSturmVariations p a - distinctSturmVariations p b := by
  let q := sturmSquarefreePart p
  have hq := hasSimpleRoots_sturmSquarefreePart p
  have hqa : ¬ q.IsRoot a := fun h ↦ ha ((isRoot_sturmSquarefreePart_iff hp a).1 h)
  have hqb : ¬ q.IsRoot b := fun h ↦ hb ((isRoot_sturmSquarefreePart_iff hp b).1 h)
  have hcount := card_roots_filter_Ioo_eq_sturmVariations_sub hq hab hqa hqb
  have hnodup := hq.roots_nodup
  calc
    distinctRootCountIoo p a b =
        (q.roots.toFinset.filter fun r ↦ a < r ∧ r < b).card := by
      simp [distinctRootCountIoo, q, roots_toFinset_sturmSquarefreePart hp]
    _ = (q.roots.filter fun r ↦ a < r ∧ r < b).card := by
      rw [← Multiset.toFinset_filter]
      exact Multiset.toFinset_card_of_nodup (hnodup.filter _)
    _ = distinctSturmVariations p a - distinctSturmVariations p b := by
      simpa [distinctSturmVariations, q] using hcount

theorem splits_sturmSquarefreePart_iff {p : ℝ[X]} (hp : p ≠ 0) :
    (sturmSquarefreePart p).Splits ↔ p.Splits := by
  constructor
  · intro hq
    obtain ⟨n, hdiv⟩ := exists_dvd_radical_self_pow hp
    exact (hq.pow n).of_dvd (pow_ne_zero n (sturmSquarefreePart_ne_zero p)) hdiv
  · intro h
    exact h.of_dvd hp (by simpa [sturmSquarefreePart] using radical_dvd_self (a := p))

/-- A bounded squarefree Sturm test for real-rootedness.  If `(a,b)` contains
every root, the polynomial is real-rooted exactly when the Sturm count equals
the degree of its squarefree part. -/
theorem splits_iff_distinctSturmVariations_sub_eq_natDegree
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ} (hab : a < b)
    (hbound : ∀ r : ℝ, p.IsRoot r → a < r ∧ r < b) :
    p.Splits ↔
      distinctSturmVariations p a - distinctSturmVariations p b =
        (sturmSquarefreePart p).natDegree := by
  have ha : ¬ p.IsRoot a := fun h ↦ (lt_irrefl a) (hbound a h).1
  have hb : ¬ p.IsRoot b := fun h ↦ (lt_irrefl b) (hbound b h).2
  rw [← splits_sturmSquarefreePart_iff hp,
    Polynomial.splits_iff_card_roots,
    ← distinctRootCountIoo_eq_distinctSturmVariations_sub hp hab ha hb]
  have hroots : distinctRootCountIoo p a b =
      (sturmSquarefreePart p).roots.card := by
    rw [← Multiset.toFinset_card_of_nodup
      (hasSimpleRoots_sturmSquarefreePart p).roots_nodup]
    unfold distinctRootCountIoo
    rw [← roots_toFinset_sturmSquarefreePart hp]
    congr 1
    apply Finset.filter_eq_self.mpr
    intro r hr
    exact hbound r <| (isRoot_sturmSquarefreePart_iff hp r).1 <|
      (Polynomial.mem_roots (sturmSquarefreePart_ne_zero p)).1 (by simpa using hr)
  rw [hroots]

end RealRooted
