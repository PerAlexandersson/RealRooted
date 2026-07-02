/-
# Product-family common interleaver theorems

zip-with-product constructions, common-interleaver outputs for product
families (Brändén Theorem 7.8.3).
-/
import RealRooted.CommonInterleaverSeq

open Polynomial

noncomputable section

namespace RealRooted

section

/-! ## Matrix action on polynomial sequences -/

lemma hasNonnegCoeffs_affine_mul {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs ((C s * X + C t) * p) := by
  have hsXp : HasNonnegCoeffs (C s * (X * p)) :=
    nonnegCoeffs_C_mul hs hp.X_mul
  have htp : HasNonnegCoeffs (C t * p) :=
    nonnegCoeffs_C_mul ht hp
  have hsum : HasNonnegCoeffs (C s * (X * p) + C t * p) := hsXp.add htp
  grind

lemma hasNonnegCoeffs_sum :
    ∀ ps : List ℝ[X], (∀ p ∈ ps, HasNonnegCoeffs p) → HasNonnegCoeffs ps.sum
  | [], _ => by simpa using hasNonnegCoeffs_zero
  | p :: ps, hps => by
      have hp : HasNonnegCoeffs p := hps p (by simp)
      have htail : HasNonnegCoeffs ps.sum :=
        hasNonnegCoeffs_sum ps (fun q hq => hps q (by simp [hq]))
      simpa using hp.add htail

/-- A finite sum of nonnegative-coefficient polynomials cannot vanish if one of
the summands is already nonzero. This is the no-cancellation fact needed when
matrix row sums are built from nonnegative product terms. -/
lemma add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
    {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hq_ne : q ≠ 0) :
    p + q ≠ 0 := by
  let d : ℕ := q.natDegree
  have hp_coeff : 0 ≤ p.coeff d := hp d
  have hq_pos : 0 < q.coeff d := by
    have hq_lc : 0 < q.leadingCoeff := hq.pos_leadingCoeff hq_ne
    simpa [d] using hq_lc
  intro hsum0
  have hcoeff0 : (p + q).coeff d = 0 := by simp_all
  rw [coeff_add] at hcoeff0
  linarith

lemma sum_ne_zero_of_hasNonnegCoeffs_of_mem_ne_zero
    {ps : List ℝ[X]} {p : ℝ[X]}
    (hps : ∀ q ∈ ps, HasNonnegCoeffs q)
    (hp_mem : p ∈ ps) (hp_ne : p ≠ 0) :
    ps.sum ≠ 0 := by
  induction ps generalizing p with
  | nil =>
      simp_all
  | cons q ps ih =>
      simp only [List.mem_cons] at hp_mem
      rcases hp_mem with rfl | hp_mem
      · have htail_nonneg : HasNonnegCoeffs ps.sum :=
          hasNonnegCoeffs_sum ps (fun r hr => hps r (by simp [hr]))
        simpa [List.sum_cons, add_comm] using
          add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
            htail_nonneg (hps p (by simp)) hp_ne
      · have htail_nonneg : HasNonnegCoeffs ps.sum :=
          hasNonnegCoeffs_sum ps (fun r hr => hps r (by simp [hr]))
        have htail_ne : ps.sum ≠ 0 :=
          ih (fun r hr => hps r (by simp [hr])) hp_mem hp_ne
        simpa [List.sum_cons] using
          add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
            (hps q (by simp)) htail_nonneg htail_ne

lemma mem_zipWith_mul {row fs : List ℝ[X]} {p : ℝ[X]}
    (hp : p ∈ row.zipWith (· * ·) fs) :
    ∃ a ∈ row, ∃ b ∈ fs, p = a * b := by
  induction row generalizing fs with
  | nil =>
      simp_all
  | cons a row ih =>
      cases fs with
      | nil =>
          simp at hp
      | cons b fs =>
          simp only [List.zipWith_cons_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · simp
          · grind

lemma mem_zipWith_mul_get {row fs : List ℝ[X]}
    (hlen : row.length = fs.length) (i : Fin row.length) :
    row.get i * fs.get ⟨i.1, by lia⟩ ∈ row.zipWith (· * ·) fs := by
  refine List.mem_iff_get.2 ?_
  refine ⟨⟨i.1, by grind⟩, ?_⟩
  simp [List.get_eq_getElem]

lemma hasNonnegCoeffs_zipWith_mul_sum {row fs : List ℝ[X]}
    (hrow : ∀ p ∈ row, HasNonnegCoeffs p)
    (hfs : ∀ f ∈ fs, HasNonnegCoeffs f) :
    HasNonnegCoeffs ((row.zipWith (· * ·) fs).sum) :=
  hasNonnegCoeffs_sum _ fun _ hp =>
    let ⟨a, ha, b, hb, hp_eq⟩ := mem_zipWith_mul hp
    hp_eq ▸ (hrow a ha).mul (hfs b hb)

/-- A zip-with product sum of nonnegative-coefficient polynomials is nonzero as
soon as one product term is nonzero. -/
lemma zipWith_mul_sum_ne_zero_of_mem_ne_zero
    {row fs : List ℝ[X]} {p : ℝ[X]}
    (hrow : ∀ q ∈ row, HasNonnegCoeffs q)
    (hfs : ∀ q ∈ fs, HasNonnegCoeffs q)
    (hp_mem : p ∈ row.zipWith (· * ·) fs)
    (hp_ne : p ≠ 0) :
    ((row.zipWith (· * ·) fs).sum) ≠ 0 :=
  sum_ne_zero_of_hasNonnegCoeffs_of_mem_ne_zero
    (ps := row.zipWith (· * ·) fs)
    (p := p)
    (fun _ hq =>
      let ⟨a, ha, b, hb, hq_def⟩ := mem_zipWith_mul hq
      hq_def ▸ (hrow a ha).mul (hfs b hb))
    hp_mem hp_ne

/-- Product-family pairwise left common interleaver from two interlacing
sequences: for `i < j`, the mixed product in the reversed family is interlaced
by the two corresponding diagonal products. This is the pairwise input for
Brändén 7.8.3. -/
theorem pairwiseHasCommonLeftInterleaver_zipWith_mul_reverse_of_interlacingSeqNonneg
    {fs gs : List ℝ[X]}
    (hlen : fs.length = gs.length)
    (hfs : IsInterlacingSeqNonneg fs)
    (hgs : IsInterlacingSeqNonneg gs) :
    PairwiseHasCommonLeftInterleaver (fs.zipWith (· * ·) gs.reverse) := by
  have hpair_fs : fs.Pairwise Prec := (isInterlacingSeq_iff_pairwise.mp hfs.2)
  have hpair_gs : gs.Pairwise Prec := (isInterlacingSeq_iff_pairwise.mp hgs.2)
  intro i j hij
  have hzip_len : (fs.zipWith (· * ·) gs.reverse).length = fs.length := by
    simp [List.length_zipWith, hlen, List.length_reverse]
  let i' : Fin fs.length := ⟨i.1, by lia⟩
  let j' : Fin fs.length := ⟨j.1, by lia⟩
  let i'' : Fin gs.reverse.length :=
    ⟨i.1, by grind⟩
  let j'' : Fin gs.reverse.length :=
    ⟨j.1, by grind⟩
  have hij' : i' < j' := hij
  have hij'' : i'' < j'' := hij
  let fi := fs.get i'
  let fj := fs.get j'
  let gi := gs.reverse.get i''
  let gj := gs.reverse.get j''
  have hi'' : i''.1 < gs.length := by lia
  have hj'' : j''.1 < gs.length := by lia
  let ki : Fin gs.length := ⟨gs.length - 1 - i''.1, by
    lia⟩
  let kj : Fin gs.length := ⟨gs.length - 1 - j''.1, by
    lia⟩
  have hkj_ki : kj < ki := by
    have hrev_idx : gs.length - 1 - j''.1 < gs.length - 1 - i''.1 := by lia
    simpa [kj, ki] using hrev_idx
  have hfi_fj : Prec fi fj := by
    simpa [fi, fj] using (List.pairwise_iff_get.mp hpair_fs i' j' hij')
  have hgj_gi : Prec gj gi := by
    rw [show gj = gs.get kj by
      simp [gj, kj]]
    rw [show gi = gs.get ki by
      simp [gi, ki]]
    exact List.pairwise_iff_get.mp hpair_gs kj ki hkj_ki
  have hfi_rr : (fi ≠ 0 ∧ fi.Splits) := hfs.realRooted fi (List.get_mem _ _)
  have hgj_rr : (gj ≠ 0 ∧ gj.Splits) := by
    rw [show gj = gs.get kj by
      simp [gj, kj]]
    exact hgs.realRooted _ (List.get_mem _ _)
  have hleft_i : Prec (fi * gj) (fi * gi) := by
    simpa [fi, gi, gj, mul_comm, mul_left_comm, mul_assoc] using
      (prec_mul_common_factor hfi_rr.1 hfi_rr.2 hgj_gi)
  have hleft_j : Prec (fi * gj) (fj * gj) := by
    simpa [fi, fj, gj, mul_comm, mul_left_comm, mul_assoc] using
      (prec_mul_common_factor hgj_rr.1 hgj_rr.2 hfi_fj)
  refine ⟨fi * gj, ?_, ?_⟩
  · simpa [List.get_eq_getElem, fi, gi, gj, i', hzip_len] using hleft_i
  · simpa [List.get_eq_getElem, fi, fj, gj, j', hzip_len] using hleft_j

/-- Product-family pairwise common right interleaver from two interlacing
sequences. For `i < j` in the reversed product family, the witness is the other
mixed product `fⱼ * g_{n-1-i}`. This matches the right-oriented
Chudnovsky--Seymour theorem already used elsewhere in the file. -/
theorem pairwiseHasCommonInterleaver_zipWith_mul_reverse_of_interlacingSeqNonneg
    {fs gs : List ℝ[X]}
    (hlen : fs.length = gs.length)
    (hfs : IsInterlacingSeqNonneg fs)
    (hgs : IsInterlacingSeqNonneg gs) :
    PairwiseHasCommonInterleaver (fs.zipWith (· * ·) gs.reverse) := by
  have hpair_fs : fs.Pairwise Prec := (isInterlacingSeq_iff_pairwise.mp hfs.2)
  have hpair_gs : gs.Pairwise Prec := (isInterlacingSeq_iff_pairwise.mp hgs.2)
  intro i j hij
  have hzip_len : (fs.zipWith (· * ·) gs.reverse).length = fs.length := by
    simp [List.length_zipWith, hlen, List.length_reverse]
  let i' : Fin fs.length := ⟨i.1, by lia⟩
  let j' : Fin fs.length := ⟨j.1, by lia⟩
  let i'' : Fin gs.reverse.length :=
    ⟨i.1, by grind⟩
  let j'' : Fin gs.reverse.length :=
    ⟨j.1, by grind⟩
  have hij' : i' < j' := hij
  let fi := fs.get i'
  let fj := fs.get j'
  let gi := gs.reverse.get i''
  let gj := gs.reverse.get j''
  have hi'' : i''.1 < gs.length := by lia
  have hj'' : j''.1 < gs.length := by lia
  let ki : Fin gs.length := ⟨gs.length - 1 - i''.1, by
    lia⟩
  let kj : Fin gs.length := ⟨gs.length - 1 - j''.1, by
    lia⟩
  have hkj_ki : kj < ki := by grind
  have hfi_fj : Prec fi fj := by
    simpa [fi, fj] using (List.pairwise_iff_get.mp hpair_fs i' j' hij')
  have hgj_gi : Prec gj gi := by
    rw [show gj = gs.get kj by
      simp [gj, kj]]
    rw [show gi = gs.get ki by
      simp [gi, ki]]
    exact List.pairwise_iff_get.mp hpair_gs kj ki hkj_ki
  have hfj_rr : (fj ≠ 0 ∧ fj.Splits) := hfs.realRooted fj (List.get_mem _ _)
  have hgi_rr : (gi ≠ 0 ∧ gi.Splits) := by
    rw [show gi = gs.get ki by
      simp [gi, ki]]
    exact hgs.realRooted _ (List.get_mem _ _)
  have hright_i : Prec (fi * gi) (fj * gi) := by
    simpa [fi, fj, gi, mul_comm, mul_left_comm, mul_assoc] using
      (prec_mul_common_factor hgi_rr.1 hgi_rr.2 hfi_fj)
  have hright_j : Prec (fj * gj) (fj * gi) := by
    simpa [fj, gi, gj, mul_comm, mul_left_comm, mul_assoc] using
      (prec_mul_common_factor hfj_rr.1 hfj_rr.2 hgj_gi)
  grind

/-- The reversed product family has a common interleaver once one upgrades the
pairwise witnesses via Chudnovsky--Seymour. This isolates the exact remaining
CS input needed for Brändén 7.8.3. -/
theorem hasCommonInterleaver_zipWith_mul_reverse_of_interlacingSeqNonneg
    {fs gs : List ℝ[X]}
    (hlen : fs.length = gs.length)
    (hfs : IsInterlacingSeqNonneg fs)
    (hgs : IsInterlacingSeqNonneg gs) :
    HasCommonInterleaver (fs.zipWith (· * ·) gs.reverse) := by
  let ps := fs.zipWith (· * ·) gs.reverse
  have hgs_rr_rev : ∀ p ∈ gs.reverse, p.Splits := fun p hp ↦ hgs.splits (by simp_all)
  have hgs_pos_rev : ∀ p ∈ gs.reverse, HasPosLeadingCoeff p :=
    fun p hp => hgs.posLeadingCoeff p (by simp_all)
  have hpair : PairwiseHasCommonInterleaver ps := by
    simpa [ps] using
      pairwiseHasCommonInterleaver_zipWith_mul_reverse_of_interlacingSeqNonneg
        (fs := fs) (gs := gs) hlen hfs hgs
  have hrr : ∀ p ∈ ps, p.Splits := by
    intro p hp
    rcases mem_zipWith_mul hp with ⟨f, hf, g, hg, rfl⟩
    exact (hfs.splits hf).mul (hgs_rr_rev g hg)
  have hpos : ∀ p ∈ ps, HasPosLeadingCoeff p := by
    intro p hp
    rcases mem_zipWith_mul hp with ⟨f, hf, g, hg, rfl⟩
    simpa [HasPosLeadingCoeff, leadingCoeff_mul] using
      mul_pos (hfs.posLeadingCoeff f hf) (hgs_pos_rev g hg)
  exact hasCommonInterleaver_of_pairwiseHasCommonInterleaver hrr hpos hpair

/-- Brändén's Lemma 7.8.3: the reversed product-sum of two interlacing
nonnegative families is real-rooted.

The remaining mathematical content here is exactly the `2 ⇒ m` direction of
Chudnovsky--Seymour's Theorem 7.8.2: the previous lemma gives pairwise common
interleavers for the product family, and one then upgrades that to a common
interleaver for the whole family before summing. -/
theorem isRealRooted_zipWith_mul_sum_reverse_of_interlacingSeqNonneg
    {fs gs : List ℝ[X]}
    (hne : fs ≠ [])
    (hlen : fs.length = gs.length)
    (hfs : IsInterlacingSeqNonneg fs)
    (hgs : IsInterlacingSeqNonneg gs) :
    (((fs.zipWith (· * ·) gs.reverse).sum) ≠ 0 ∧
      ((fs.zipWith (· * ·) gs.reverse).sum).Splits) := by
  let ps := fs.zipWith (· * ·) gs.reverse
  have hpos : ∀ p ∈ ps, HasPosLeadingCoeff p := by
    intro p hp
    rcases mem_zipWith_mul hp with ⟨f, hf, g, hg, rfl⟩
    have hg_pos_rev : HasPosLeadingCoeff g :=
      hgs.posLeadingCoeff g (by simp_all)
    simpa [HasPosLeadingCoeff, leadingCoeff_mul] using
      mul_pos (hfs.posLeadingCoeff f hf) hg_pos_rev
  have hps_ne : ps ≠ [] := by
    intro hnil
    have hlen_ps : ps.length = fs.length := by
      simp [ps, List.length_zipWith, hlen, List.length_reverse]
    grind
  exact
    isRealRooted_sum_of_commonInterleaver
      (by
        simpa [ps] using
          hasCommonInterleaver_zipWith_mul_reverse_of_interlacingSeqNonneg
            (fs := fs) (gs := gs) hlen hfs hgs)
      hpos
      hps_ne

/-- Paired filter used by the weak zero-aware product-sum wrapper: keep the
pairs whose left component is nonzero. -/
def filterLeftNonzeroPairs (fs gs : List ℝ[X]) : List (ℝ[X] × ℝ[X]) :=
  (fs.zip gs).filter fun p => p.1 ≠ 0

def filterLeftNonzero (fs gs : List ℝ[X]) : List ℝ[X] :=
  (filterLeftNonzeroPairs fs gs).map Prod.fst

def filterRightByLeftNonzero (fs gs : List ℝ[X]) : List ℝ[X] :=
  (filterLeftNonzeroPairs fs gs).map Prod.snd

lemma length_filterLeftNonzero_eq_filterRightByLeftNonzero
    (fs gs : List ℝ[X]) :
    (filterLeftNonzero fs gs).length = (filterRightByLeftNonzero fs gs).length := by
  simp [filterLeftNonzero, filterRightByLeftNonzero]

lemma filterLeftNonzero_eq_filter_ne_zero {fs gs : List ℝ[X]}
    (hlen : fs.length = gs.length) :
    filterLeftNonzero fs gs = fs.filter (· ≠ 0) := by
  induction fs generalizing gs with
  | nil =>
      cases gs <;> simp [filterLeftNonzero, filterLeftNonzeroPairs] at hlen ⊢
  | cons f fs ih =>
      cases gs with
      | nil =>
          simp at hlen
      | cons g gs =>
          simp at hlen
          by_cases hf : f = 0
          · simp [filterLeftNonzero, filterLeftNonzeroPairs, hf]
            simpa [filterLeftNonzero, filterLeftNonzeroPairs] using ih hlen
          · simp [filterLeftNonzero, filterLeftNonzeroPairs, hf]
            simpa [filterLeftNonzero, filterLeftNonzeroPairs] using ih hlen

lemma filterRightByLeftNonzero_sublist_right (fs gs : List ℝ[X]) :
    (filterRightByLeftNonzero fs gs).Sublist gs := by
  induction fs generalizing gs with
  | nil =>
      cases gs <;> simp [filterRightByLeftNonzero, filterLeftNonzeroPairs]
  | cons f fs ih =>
      cases gs with
      | nil =>
          simp [filterRightByLeftNonzero, filterLeftNonzeroPairs]
      | cons g gs =>
          by_cases hf : f = 0
          · simp [filterRightByLeftNonzero, filterLeftNonzeroPairs, hf]
            simpa [filterRightByLeftNonzero, filterLeftNonzeroPairs] using (ih gs).cons g
          · simp [filterRightByLeftNonzero, filterLeftNonzeroPairs, hf]
            simpa [filterRightByLeftNonzero, filterLeftNonzeroPairs] using ih gs

lemma zipWith_mul_sum_filterLeftNonzero_eq
    (fs gs : List ℝ[X]) :
    ((filterLeftNonzero fs gs).zipWith (· * ·) (filterRightByLeftNonzero fs gs)).sum =
      (fs.zipWith (· * ·) gs).sum := by
  induction fs generalizing gs with
  | nil =>
      cases gs <;> simp [filterLeftNonzero, filterRightByLeftNonzero, filterLeftNonzeroPairs]
  | cons f fs ih =>
      cases gs with
      | nil =>
          simp [filterLeftNonzero, filterRightByLeftNonzero, filterLeftNonzeroPairs]
      | cons g gs =>
          by_cases hf : f = 0
          · simp [filterLeftNonzero, filterRightByLeftNonzero, filterLeftNonzeroPairs, hf]
            simpa [filterLeftNonzero, filterRightByLeftNonzero, filterLeftNonzeroPairs] using ih gs
          · simp [filterLeftNonzero, filterRightByLeftNonzero, filterLeftNonzeroPairs, hf]
            simpa [filterLeftNonzero, filterRightByLeftNonzero, filterLeftNonzeroPairs] using ih gs

def filterProductNonzeroPairs (fs gs : List ℝ[X]) : List (ℝ[X] × ℝ[X]) :=
  (fs.zip gs).filter fun p => p.1 ≠ 0 ∧ p.2 ≠ 0

def filterProductLeftNonzero (fs gs : List ℝ[X]) : List ℝ[X] :=
  (filterProductNonzeroPairs fs gs).map Prod.fst

def filterProductRightNonzero (fs gs : List ℝ[X]) : List ℝ[X] :=
  (filterProductNonzeroPairs fs gs).map Prod.snd

lemma length_filterProductLeftNonzero_eq_filterProductRightNonzero
    (fs gs : List ℝ[X]) :
    (filterProductLeftNonzero fs gs).length =
      (filterProductRightNonzero fs gs).length := by
  simp [filterProductLeftNonzero, filterProductRightNonzero]

lemma filterProductLeftNonzero_sublist_left (fs gs : List ℝ[X]) :
    (filterProductLeftNonzero fs gs).Sublist fs := by
  induction fs generalizing gs with
  | nil =>
      cases gs <;> simp [filterProductLeftNonzero, filterProductNonzeroPairs]
  | cons f fs ih =>
      cases gs with
      | nil =>
          simp [filterProductLeftNonzero, filterProductNonzeroPairs]
      | cons g gs =>
          by_cases hfg : f ≠ 0 ∧ g ≠ 0
          · simp [filterProductLeftNonzero, filterProductNonzeroPairs, hfg]
            simpa [filterProductLeftNonzero, filterProductNonzeroPairs] using ih gs
          · simp [filterProductLeftNonzero, filterProductNonzeroPairs, hfg]
            simpa [filterProductLeftNonzero, filterProductNonzeroPairs] using
              (ih gs).cons f

lemma filterProductRightNonzero_sublist_right (fs gs : List ℝ[X]) :
    (filterProductRightNonzero fs gs).Sublist gs := by
  induction fs generalizing gs with
  | nil =>
      cases gs <;> simp [filterProductRightNonzero, filterProductNonzeroPairs]
  | cons f fs ih =>
      cases gs with
      | nil =>
          simp [filterProductRightNonzero, filterProductNonzeroPairs]
      | cons g gs =>
          by_cases hfg : f ≠ 0 ∧ g ≠ 0
          · simp [filterProductRightNonzero, filterProductNonzeroPairs, hfg]
            simpa [filterProductRightNonzero, filterProductNonzeroPairs] using ih gs
          · simp [filterProductRightNonzero, filterProductNonzeroPairs, hfg]
            simpa [filterProductRightNonzero, filterProductNonzeroPairs] using
              (ih gs).cons g

lemma mem_filterProductLeftNonzero_ne_zero {fs gs : List ℝ[X]} {f : ℝ[X]}
    (hf : f ∈ filterProductLeftNonzero fs gs) : f ≠ 0 := by
  rcases List.mem_map.1 hf with ⟨p, hp, rfl⟩
  exact (of_decide_eq_true (List.mem_filter.1 hp).2).1

lemma mem_filterProductRightNonzero_ne_zero {fs gs : List ℝ[X]} {g : ℝ[X]}
    (hg : g ∈ filterProductRightNonzero fs gs) : g ≠ 0 := by
  rcases List.mem_map.1 hg with ⟨p, hp, rfl⟩
  exact (of_decide_eq_true (List.mem_filter.1 hp).2).2

lemma zipWith_mul_sum_filterProductNonzero_eq
    (fs gs : List ℝ[X]) :
    ((filterProductLeftNonzero fs gs).zipWith (· * ·)
      (filterProductRightNonzero fs gs)).sum =
      (fs.zipWith (· * ·) gs).sum := by
  induction fs generalizing gs with
  | nil =>
      cases gs <;> simp [filterProductLeftNonzero, filterProductRightNonzero,
        filterProductNonzeroPairs]
  | cons f fs ih =>
      cases gs with
      | nil =>
          simp [filterProductLeftNonzero, filterProductRightNonzero,
            filterProductNonzeroPairs]
      | cons g gs =>
          by_cases hfg : f ≠ 0 ∧ g ≠ 0
          · simp [filterProductLeftNonzero, filterProductRightNonzero,
              filterProductNonzeroPairs, hfg]
            simpa [filterProductLeftNonzero, filterProductRightNonzero,
              filterProductNonzeroPairs] using ih gs
          · have hprod : f * g = 0 := by grind
            simp [filterProductLeftNonzero, filterProductRightNonzero,
              filterProductNonzeroPairs, hfg, hprod]
            simpa [filterProductLeftNonzero, filterProductRightNonzero,
              filterProductNonzeroPairs] using ih gs

/-- Weak zero-aware product-sum theorem. If the left family is weakly
interlacing, its nonzero members are real-rooted, and the paired product sum is
nonzero, then filtering out zero left factors lets us reuse Brändén's strict
product-sum theorem. -/
theorem isRealRooted_zipWith_mul_sum_reverse_of_interlacingSeq0Nonneg
    {fs gs : List ℝ[X]}
    (hlen : fs.length = gs.length)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hgs : IsInterlacingSeqNonneg gs)
    (hsum_ne : (fs.zipWith (· * ·) gs.reverse).sum ≠ 0) :
    (((fs.zipWith (· * ·) gs.reverse).sum) ≠ 0 ∧
      ((fs.zipWith (· * ·) gs.reverse).sum).Splits) := by
  let fs' := filterLeftNonzero fs gs.reverse
  let gs' := filterRightByLeftNonzero fs gs.reverse
  have hfs'_eq : fs' = fs.filter (· ≠ 0) := by
    simpa [fs'] using
      filterLeftNonzero_eq_filter_ne_zero
        (fs := fs) (gs := gs.reverse) (by simp_all)
  have hfs' : IsInterlacingSeqNonneg fs' := by
    rw [hfs'_eq]
    exact IsInterlacingSeq0Nonneg.filter_ne_zero_of_realRooted hfs hfs_real
  have hgs'_rev : IsInterlacingSeqNonneg gs'.reverse := by
    have hsub : gs'.Sublist gs.reverse := by
      simpa [gs'] using filterRightByLeftNonzero_sublist_right fs gs.reverse
    have hsub_rev : gs'.reverse.Sublist gs := by grind
    exact IsInterlacingSeqNonneg.sublist hgs hsub_rev
  have hlen' : fs'.length = gs'.length := by
    simpa [fs', gs'] using length_filterLeftNonzero_eq_filterRightByLeftNonzero fs gs.reverse
  have hsum_eq :
      (fs'.zipWith (· * ·) gs').sum = (fs.zipWith (· * ·) gs.reverse).sum := by
    simpa [fs', gs'] using zipWith_mul_sum_filterLeftNonzero_eq fs gs.reverse
  have hfs'_ne : fs' ≠ [] := fun hnil => by simp_all
  have hrr :
      (((fs'.zipWith (· * ·) (gs'.reverse).reverse).sum) ≠ 0 ∧
        ((fs'.zipWith (· * ·) (gs'.reverse).reverse).sum).Splits) :=
    isRealRooted_zipWith_mul_sum_reverse_of_interlacingSeqNonneg
      (fs := fs') (gs := gs'.reverse)
      hfs'_ne
      (by simp_all)
      hfs'
      hgs'_rev
  simp_all

/-- Two-sided weak zero-aware product-sum theorem. Zero factors on either side
are removed pairwise before applying Brändén's strict product-sum theorem. -/
theorem isRealRooted_zipWith_mul_sum_reverse_of_interlacingSeq0Nonneg_both
    {fs gs : List ℝ[X]}
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hgs : IsInterlacingSeq0Nonneg gs)
    (hgs_real : ∀ g ∈ gs, g ≠ 0 → (g ≠ 0 ∧ g.Splits))
    (hsum_ne : (fs.zipWith (· * ·) gs.reverse).sum ≠ 0) :
    (((fs.zipWith (· * ·) gs.reverse).sum) ≠ 0 ∧
      ((fs.zipWith (· * ·) gs.reverse).sum).Splits) := by
  let fs' := filterProductLeftNonzero fs gs.reverse
  let gs' := filterProductRightNonzero fs gs.reverse
  have hfs_sub : fs'.Sublist fs := by
    simpa [fs'] using filterProductLeftNonzero_sublist_left fs gs.reverse
  have hgs_sub_rev : gs'.reverse.Sublist gs := by
    have hsub : gs'.Sublist gs.reverse := by
      simpa [gs'] using filterProductRightNonzero_sublist_right fs gs.reverse
    grind
  have hfs' : IsInterlacingSeqNonneg fs' :=
    hfs.sublist_of_realRooted_of_ne hfs_sub hfs_real
      (fun f hf => mem_filterProductLeftNonzero_ne_zero (fs := fs) (gs := gs.reverse) hf)
  have hgs'_rev : IsInterlacingSeqNonneg gs'.reverse :=
    hgs.sublist_of_realRooted_of_ne hgs_sub_rev hgs_real
      (fun g hg =>
        mem_filterProductRightNonzero_ne_zero
          (fs := fs) (gs := gs.reverse) (by grind))
  have hlen' : fs'.length = gs'.length := by
    simpa [fs', gs'] using length_filterProductLeftNonzero_eq_filterProductRightNonzero
      fs gs.reverse
  have hsum_eq :
      (fs'.zipWith (· * ·) gs').sum = (fs.zipWith (· * ·) gs.reverse).sum := by
    simpa [fs', gs'] using zipWith_mul_sum_filterProductNonzero_eq fs gs.reverse
  have hfs'_ne : fs' ≠ [] := fun hnil => by simp_all
  have hrr :
      (((fs'.zipWith (· * ·) (gs'.reverse).reverse).sum) ≠ 0 ∧
        ((fs'.zipWith (· * ·) (gs'.reverse).reverse).sum).Splits) :=
    isRealRooted_zipWith_mul_sum_reverse_of_interlacingSeqNonneg
      (fs := fs') (gs := gs'.reverse)
      hfs'_ne
      (by simp_all)
      hfs'
      hgs'_rev
  simp_all

end
end RealRooted
