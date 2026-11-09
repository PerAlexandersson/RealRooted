module

public import RealRooted.Compatibility.Basic
public import RealRooted.CommonInterleaver.RootDesc
public import RealRooted.RootLocation.Basic
import RealRooted.ChudnovskySeymour.Core
import RealRooted.CommonInterleaver.PairwiseUpgrade.FamilyCompatibility
import RealRooted.CommonInterleaver.SuccDegreeLowDegree

/-!
# Transport of common interleavers along linear maps

Let `J` be an interval and `n` a degree.  A linear map `T` on real polynomials *maps
positive-leading degree-`n` polynomials rooted in `J` to real-rooted ones*
(`MapsPosRealRootedIn T n J`) if it sends every such polynomial to a polynomial with positive
leading coefficient which splits over `ℝ`.

* `isRealRootedIn_weightedSum_of_splits`: a nonnegative combination of positive-leading
  degree-`n` polynomials rooted in an interval `J` is rooted in `J` as soon as it splits.  Outside
  the convex hull of all roots, every member has the sign of `(-1)^n` or of `1`, according to the
  side, so the combination cannot vanish there.
* `FamilyCompatible.map`, `HasCommonInterleaver.map`: such a map transports a compatible family, or
  a common interleaver, of inputs rooted in `J` to the images.  The proof combines the hull lemma
  with the Chudnovsky--Seymour theorem: every nonnegative combination of the inputs splits, hence
  is rooted in `J`, hence has a real-rooted image; the image of a combination is the combination
  of the images by linearity, so the images form a compatible family and have a common interleaver
  (Chudnovsky--Seymour; this is the criterion of Marcus--Spielman--Srivastava, *Interlacing
  families I*, Lemma 4.5).

The output degree need not be constant, and the common leading-coefficient sign is normalised to
be positive (replace `T` by `-T` for the negative sign).  The conclusion is a common interleaver,
not a directed alternation of the two image lists.
-/

@[expose] public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-! ### Hull lemma -/

section Hull

variable {J : Set ℝ} {x : ℝ}

/-- Multiset identity: `∏ (x - r) = (-1)^card * ∏ (r - x)`. -/
private theorem prod_map_sub_eq (s : Multiset ℝ) :
    (s.map (x - ·)).prod = (-1) ^ Multiset.card s * (s.map (· - x)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih, pow_succ]
    ring

/-- A positive-leading split polynomial of degree `n` has `eval x` of sign `1` to the right of all
its roots. -/
private theorem eval_pos_of_forall_roots_lt {f : ℝ[X]} (hs : f.Splits)
    (hpos : HasPosLeadingCoeff f) (hx : ∀ r ∈ f.roots, r < x) : 0 < f.eval x := by
  rw [hs.eval_eq_prod_roots]
  refine mul_pos hpos (Multiset.prod_pos ?_)
  intro a ha
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 ha
  linarith [hx r hr]

/-- A positive-leading split polynomial of degree `n` has `eval x` of sign `(-1)^n` to the left
of all its roots. -/
private theorem eval_pos_of_forall_lt_roots {f : ℝ[X]} (hs : f.Splits)
    (hpos : HasPosLeadingCoeff f) (hx : ∀ r ∈ f.roots, x < r) :
    0 < (-1) ^ f.natDegree * f.eval x := by
  rw [hs.eval_eq_prod_roots, prod_map_sub_eq, ← hs.natDegree_eq_card_roots]
  have hp : 0 < (f.roots.map (· - x)).prod := by
    refine Multiset.prod_pos ?_
    intro a ha
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 ha
    linarith [hx r hr]
  have h1 : ((-1 : ℝ) ^ f.natDegree) * ((-1) ^ f.natDegree) = 1 := by
    rw [← mul_pow]; simp
  calc 0 < f.leadingCoeff * (f.roots.map (· - x)).prod := mul_pos hpos hp
    _ = _ := by linear_combination (-(f.leadingCoeff * (f.roots.map (· - x)).prod)) * h1

/-- Sign propagation for nonnegative combinations: if `ε * eval x f > 0` for each member, then
`ε * eval x` of the combination is nonnegative, and positive as soon as one weight is positive. -/
private theorem eval_weightedSum_sign (ε : ℝ) :
    ∀ l : List (ℝ × ℝ[X]), (∀ ap ∈ l, 0 ≤ ap.1) → (∀ ap ∈ l, 0 < ε * ap.2.eval x) →
      0 ≤ ε * (weightedSum l).eval x ∧
        ((∃ ap ∈ l, 0 < ap.1) → 0 < ε * (weightedSum l).eval x)
  | [], _, _ => by simp
  | (a, p) :: l, hnn, hsg => by
    have ha : 0 ≤ a := hnn (a, p) (by simp)
    have hp : 0 < ε * p.eval x := hsg (a, p) (by simp)
    obtain ⟨ih1, ih2⟩ := eval_weightedSum_sign ε l (fun ap hap => hnn ap (by simp [hap]))
      (fun ap hap => hsg ap (by simp [hap]))
    have heq : ε * (weightedSum ((a, p) :: l)).eval x =
        a * (ε * p.eval x) + ε * (weightedSum l).eval x := by
      simp only [weightedSum_cons, eval_add, eval_mul, eval_C]; ring
    refine ⟨heq ▸ by positivity, ?_⟩
    rintro ⟨⟨b, q⟩, hbq, hb⟩
    rw [heq]
    rcases List.mem_cons.1 hbq with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      have := mul_pos hb hp
      linarith
    · have hbq' : 0 < ε * (weightedSum l).eval x := ih2 ⟨(b, q), h, hb⟩
      have := mul_nonneg ha hp.le
      linarith

/-- **Hull lemma.** A nonnegative combination, with some positive weight, of positive-leading
polynomials of one degree `n` that are rooted in an interval `J` is rooted in `J` as soon as it
splits.  Outside `J` all the members have the same strict sign, `1` on the right and `(-1)^n` on
the left, so the combination cannot vanish there. -/
theorem isRealRootedIn_weightedSum_of_splits (hJ : J.OrdConnected) {n : ℕ}
    {l : List (ℝ × ℝ[X])} (hrr : ∀ ap ∈ l, IsRealRootedIn J ap.2)
    (hdeg : ∀ ap ∈ l, ap.2.natDegree = n) (hpos : ∀ ap ∈ l, HasPosLeadingCoeff ap.2)
    (hnn : ∀ ap ∈ l, 0 ≤ ap.1) (hex : ∃ ap ∈ l, 0 < ap.1)
    (hs : (weightedSum l).Splits) : IsRealRootedIn J (weightedSum l) := by
  have hne : weightedSum l ≠ 0 :=
    leadingCoeff_ne_zero.1 (hasPosLeadingCoeff_weightedSum l hnn hpos hex).ne'
  refine ⟨hne, hs, fun x hx => ?_⟩
  by_contra hxJ
  have hroot : (weightedSum l).eval x = 0 := (mem_roots hne).1 hx
  have hne_x : ∀ ap ∈ l, ∀ r ∈ ap.2.roots, r ≠ x := fun ap hap r hr hrx =>
    hxJ (hrx ▸ (hrr ap hap).mem_of_mem_roots hr)
  by_cases hA : ∀ ap ∈ l, ∀ r ∈ ap.2.roots, r < x
  · have hsg : ∀ ap ∈ l, 0 < (1 : ℝ) * ap.2.eval x := fun ap hap => by
      simpa using eval_pos_of_forall_roots_lt (hrr ap hap).splits (hpos ap hap) (hA ap hap)
    have := (eval_weightedSum_sign 1 l hnn hsg).2 hex
    simp [hroot] at this
  · push Not at hA
    obtain ⟨ap, hap, r, hr, hrx⟩ := hA
    have hxr : x < r := lt_of_le_of_ne hrx (hne_x ap hap r hr).symm
    have hB : ∀ bq ∈ l, ∀ s ∈ bq.2.roots, x < s := by
      intro bq hbq s hs'
      by_contra hsx
      have hsx' : s < x := lt_of_le_of_ne (not_lt.1 hsx) (hne_x bq hbq s hs')
      exact hxJ (hJ.out ((hrr bq hbq).mem_of_mem_roots hs')
        ((hrr ap hap).mem_of_mem_roots hr) ⟨hsx'.le, hxr.le⟩)
    have hsg : ∀ bq ∈ l, 0 < (-1 : ℝ) ^ n * bq.2.eval x := fun bq hbq => by
      simpa [hdeg bq hbq] using
        eval_pos_of_forall_lt_roots (hrr bq hbq).splits (hpos bq hbq) (hB bq hbq)
    have := (eval_weightedSum_sign ((-1) ^ n) l hnn hsg).2 hex
    simp [hroot] at this

end Hull

/-! ### Linear images of weighted sums -/

/-- A linear map sends a weighted sum to the weighted sum of the images. -/
theorem map_weightedSum (T : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    ∀ l : List (ℝ × ℝ[X]),
      T (weightedSum l) = weightedSum (l.map fun ap => (ap.1, T ap.2))
  | [] => by simp
  | (a, p) :: l => by
    simp only [weightedSum_cons, map_add, List.map_cons, map_weightedSum T l, C_mul',
      LinearMap.map_smul]

/-- Every list of nonnegative-weighted members of `fs.map T` is the image of a list over `fs`. -/
private theorem exists_preimage_list (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (fs : List ℝ[X]) :
    ∀ l : List (ℝ × ℝ[X]), (∀ ap ∈ l, ap.2 ∈ fs.map T) →
      ∃ l' : List (ℝ × ℝ[X]), (∀ ap ∈ l', ap.2 ∈ fs) ∧
        l = l'.map (fun ap => (ap.1, T ap.2))
  | [], _ => ⟨[], by simp, rfl⟩
  | (a, p) :: l, hmem => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 (hmem (a, p) (by simp))
    obtain ⟨l', hl', rfl⟩ := exists_preimage_list T fs l fun ap hap => hmem ap (by simp [hap])
    exact ⟨(a, f) :: l', by simpa [hf] using hl', rfl⟩

/-! ### Transport -/

/-- `MapsPosRealRootedIn T n J`: the linear map `T` sends every polynomial of degree `n` with
positive leading coefficient which is rooted in `J` to a polynomial with positive leading
coefficient which splits over `ℝ`. -/
def MapsPosRealRootedIn (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (n : ℕ) (J : Set ℝ) : Prop :=
  ∀ p : ℝ[X], p.natDegree = n → HasPosLeadingCoeff p → IsRealRootedIn J p →
    HasPosLeadingCoeff (T p) ∧ (T p).Splits

namespace MapsPosRealRootedIn

variable {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {n : ℕ} {J : Set ℝ} {fs : List ℝ[X]}

/-- The images of the members of a family of positive-leading degree-`n` polynomials rooted in `J`
are nonzero and split. -/
theorem ne_zero_and_splits (hT : MapsPosRealRootedIn T n J)
    (hfs : ∀ f ∈ fs, IsRealRootedIn J f ∧ f.natDegree = n ∧ HasPosLeadingCoeff f) :
    ∀ g ∈ fs.map T, g ≠ 0 ∧ g.Splits := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  obtain ⟨hrr, hdeg, hpos⟩ := hfs f hf
  obtain ⟨hp, hsp⟩ := hT f hdeg hpos hrr
  exact ⟨leadingCoeff_ne_zero.1 hp.ne', hsp⟩

/-- The images of the members of a family of positive-leading degree-`n` polynomials rooted in `J`
have positive leading coefficients. -/
theorem hasPosLeadingCoeff (hT : MapsPosRealRootedIn T n J)
    (hfs : ∀ f ∈ fs, IsRealRootedIn J f ∧ f.natDegree = n ∧ HasPosLeadingCoeff f) :
    ∀ g ∈ fs.map T, HasPosLeadingCoeff g := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
  obtain ⟨hrr, hdeg, hpos⟩ := hfs f hf
  exact (hT f hdeg hpos hrr).1

end MapsPosRealRootedIn

/-- **Transport of compatible families.**  A linear map sending positive-leading degree-`n`
polynomials rooted in an interval `J` to real-rooted ones with positive leading coefficient sends a
Chudnovsky--Seymour-compatible family of such inputs to a compatible family: every nonnegative
combination of the inputs is real-rooted, hence rooted in `J` by the hull lemma
`isRealRootedIn_weightedSum_of_splits`, hence has a real-rooted image, and the image of the
combination is the combination of the images. -/
theorem FamilyCompatible.map {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {J : Set ℝ} (hJ : J.OrdConnected) {n : ℕ}
    (hT : MapsPosRealRootedIn T n J) {fs : List ℝ[X]}
    (hfs : ∀ f ∈ fs, IsRealRootedIn J f ∧ f.natDegree = n ∧ HasPosLeadingCoeff f)
    (hfam : FamilyCompatible fs) : FamilyCompatible (fs.map T) := by
  intro l hmem hnn
  obtain ⟨l', hl', rfl⟩ := exists_preimage_list T fs l hmem
  have hnn' : ∀ ap ∈ l', 0 ≤ ap.1 := fun ap hap =>
    hnn (ap.1, T ap.2) (List.mem_map.2 ⟨ap, hap, rfl⟩)
  rw [← map_weightedSum]
  rcases hfam l' hl' hnn' with h0 | ⟨hne, hsp⟩
  · exact Or.inl (by simp [h0])
  · have hex : ∃ ap ∈ l', 0 < ap.1 := by
      by_contra hno
      exact hne (weightedSum_eq_zero_of_forall_coeff_zero l' fun ap hap =>
        le_antisymm (not_lt.1 fun hlt => hno ⟨ap, hap, hlt⟩) (hnn' ap hap))
    have hroot := isRealRootedIn_weightedSum_of_splits hJ (n := n)
      (fun ap hap => (hfs ap.2 (hl' ap hap)).1) (fun ap hap => (hfs ap.2 (hl' ap hap)).2.1)
      (fun ap hap => (hfs ap.2 (hl' ap hap)).2.2) hnn' hex hsp
    have hdeg := natDegree_weightedSum_eq_of_nonneg_of_sameDegree hnn'
      (fun ap hap => (hfs ap.2 (hl' ap hap)).2.1) (fun ap hap => (hfs ap.2 (hl' ap hap)).2.2) hex
    have hposs := hasPosLeadingCoeff_weightedSum l' hnn'
      (fun ap hap => (hfs ap.2 (hl' ap hap)).2.2) hex
    obtain ⟨hp, hsp'⟩ := hT _ hdeg hposs hroot
    exact Or.inr ⟨leadingCoeff_ne_zero.1 hp.ne', hsp'⟩

/-- **Transport of common interleavers.**  Let `T` be a linear map sending positive-leading
degree-`n` polynomials rooted in an interval `J` to real-rooted ones with positive leading
coefficient.  If a finite family of such inputs has a common interleaver, then so has the family
of its images.  By Chudnovsky--Seymour the input family is compatible; its images are compatible
by `FamilyCompatible.map`, hence have a common interleaver by Chudnovsky--Seymour again (the
criterion of Marcus--Spielman--Srivastava, *Interlacing families I*, Lemma 4.5). -/
theorem HasCommonInterleaver.map {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {J : Set ℝ} (hJ : J.OrdConnected)
    {n : ℕ} (hT : MapsPosRealRootedIn T n J) {fs : List ℝ[X]}
    (hfs : ∀ f ∈ fs, IsRealRootedIn J f ∧ f.natDegree = n ∧ HasPosLeadingCoeff f)
    (hc : HasCommonInterleaver fs) : HasCommonInterleaver (fs.map T) := by
  have hfam : FamilyCompatible fs :=
    familyCompatible_of_commonInterleaver hc fun f hf => (hfs f hf).2.2
  exact (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver
    (hT.ne_zero_and_splits hfs) (hT.hasPosLeadingCoeff hfs)).1
    (pairwiseCompatible_of_familyCompatible (hfam.map hJ hT hfs))

/-- Transport of pairwise compatibility to a common interleaver of the images: if a finite family
of positive-leading degree-`n` polynomials rooted in an interval `J` is pairwise compatible, the
images under `T` have a common interleaver. -/
theorem PairwiseCompatible.hasCommonInterleaver_map {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {J : Set ℝ}
    (hJ : J.OrdConnected) {n : ℕ} (hT : MapsPosRealRootedIn T n J) {fs : List ℝ[X]}
    (hfs : ∀ f ∈ fs, IsRealRootedIn J f ∧ f.natDegree = n ∧ HasPosLeadingCoeff f)
    (hpair : PairwiseCompatible fs) : HasCommonInterleaver (fs.map T) :=
  HasCommonInterleaver.map hJ hT hfs <|
    (chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver
      (fun f hf => ⟨(hfs f hf).1.ne_zero, (hfs f hf).1.splits⟩)
      fun f hf => (hfs f hf).2.2).1 hpair

/-- **Pairs.**  If two positive-leading degree-`n` polynomials rooted in an interval `J` are
compatible (for instance if one interlaces the other), their images under `T` have a common
interleaver. -/
theorem Compatible.hasCommonInterleaver_map {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {J : Set ℝ}
    (hJ : J.OrdConnected) {n : ℕ} (hT : MapsPosRealRootedIn T n J) {f g : ℝ[X]}
    (hf : IsRealRootedIn J f) (hfd : f.natDegree = n) (hfp : HasPosLeadingCoeff f)
    (hg : IsRealRootedIn J g) (hgd : g.natDegree = n) (hgp : HasPosLeadingCoeff g)
    (hfg : Compatible f g) : HasCommonInterleaver [T f, T g] := by
  have hfs : ∀ h ∈ [f, g], IsRealRootedIn J h ∧ h.natDegree = n ∧ HasPosLeadingCoeff h := by
    simp [hf, hfd, hfp, hg, hgd, hgp]
  have := PairwiseCompatible.hasCommonInterleaver_map hJ hT hfs (fs := [f, g]) (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all)
  simpa using this

/-- **Interlacing pairs.**  If `f ≪ g` are positive-leading degree-`n` polynomials rooted in an
interval `J`, their images under `T` have a common interleaver. -/
theorem StrictInterl.hasCommonInterleaver_map {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {J : Set ℝ}
    (hJ : J.OrdConnected) {n : ℕ} (hT : MapsPosRealRootedIn T n J) {f g : ℝ[X]}
    (hfg : StrictInterl f g) (hf : IsRealRootedIn J f) (hfd : f.natDegree = n)
    (hfp : HasPosLeadingCoeff f) (hg : IsRealRootedIn J g) (hgd : g.natDegree = n)
    (hgp : HasPosLeadingCoeff g) : HasCommonInterleaver [T f, T g] :=
  Compatible.hasCommonInterleaver_map hJ hT hf hfd hfp hg hgd hgp
    (Compatible.of_strictInterl hfg)

end RealRooted
