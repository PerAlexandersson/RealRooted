module

public import RealRooted.PFPolynomial
public import RealRooted.Compatibility.Pair
import RealRooted.ChudnovskySeymour.PF
import RealRooted.Interlacing.ResidueCriterion
import RealRooted.Interlacing.Residue
import RealRooted.PFPolynomial.PreserverClosure
import RealRooted.PFPolynomial.Closure
import RealRooted.QuadraticInterlacing.Basic
import RealRooted.WagnerX.AffineFactors
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations
import RealRooted.Linear
import RealRooted.Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Common-input reduction for operator rows

Source: unpublished manuscript, `shifted-operator-row-reduction.md`, general row reduction
and its degree-bounded version; RealRooted issue #1781. The operators are arbitrary real-linear
maps, with no commutation or output degree assumption.
-/

public section

open Polynomial Filter Topology

noncomputable section

namespace RealRooted.OperatorMatrix

private lemma pf_combo {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : Compatible f g) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsPFPolynomial (C a * f + C b * g) :=
  IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    ((hasNonnegCoeffs_C_mul ha hf.hasNonnegCoeffs).add
      (hasNonnegCoeffs_C_mul hb hg.hasNonnegCoeffs))
    ((hfg a b ha hb).imp_right And.right)

private lemma compatible_of_pf_combo {f g : ℝ[X]}
    (h : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IsPFPolynomial (C a * f + C b * g)) :
    Compatible f g := by
  intro a b ha hb
  by_cases hz : C a * f + C b * g = 0
  · exact Or.inl hz
  · exact Or.inr ((h a b ha hb).ne_zero_and_splits hz)

private lemma compatible_of_pf_pos {f g : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (h : ∀ r : ℝ, 0 < r → IsPFPolynomial (C r * f + g)) : Compatible f g := by
  apply compatible_of_pf_combo
  intro a b ha hb
  rcases eq_or_lt_of_le ha with rfl | ha
  · simpa using (IsPFPolynomial.of_C_nonneg hb).mul hg
  rcases eq_or_lt_of_le hb with rfl | hb
  · simpa using (IsPFPolynomial.of_C_nonneg ha.le).mul hf
  have heq : C a * f + C b * g = C b * (C (a / b) * f + g) := by
    rw [mul_add, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ hb.ne']
  rw [heq]
  exact (h (a / b) (div_pos ha hb)).const_mul hb

/-- For PF endpoints, compatibility is equivalent to all positive ratio combinations being PF.
Zero combination weights are supplied by the endpoints. -/
theorem compatible_iff_isPFPolynomial_pos {f g : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) :
    Compatible f g ↔ ∀ r : ℝ, 0 < r → IsPFPolynomial (C r * f + g) := by
  refine ⟨fun h r hr => ?_, compatible_of_pf_pos hf hg⟩
  simpa using pf_combo hf hg h hr.le zero_le_one

private lemma map_C_mul (A : ℝ[X] →ₗ[ℝ] ℝ[X]) (a : ℝ) (p : ℝ[X]) :
    A (C a * p) = C a * A p := by
  rw [← smul_eq_C_mul, A.map_smul, smul_eq_C_mul]

private lemma compatible_map {N : ℕ} (A : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hA : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (A p))
    {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree ≤ N) (hfg : Compatible f g) :
    Compatible (A f) (A g) := by
  apply compatible_of_pf_combo
  intro a b ha hb
  rw [← map_C_mul, ← map_C_mul, ← map_add]
  exact hA _ (pf_combo hf hg hfg ha hb) ((natDegree_add_le _ _).trans
    (max_le ((natDegree_C_mul_le _ _).trans hfN) ((natDegree_C_mul_le _ _).trans hgN)))

/-- The oriented cofactor expansion includes the polynomial part for equal-degree pairs. -/
private lemma exists_cofactor_expansion {p q : ℝ[X]} (hp : IsPFPolynomial p)
    (hq : IsPFPolynomial q) (hpq : StrictInterl p q) (hqnd : q.roots.Nodup)
    (hqdeg : 1 ≤ q.natDegree) :
    ∃ a : ℝ, 0 ≤ a ∧
      p = C a * q + ∑ r ∈ q.roots.toFinset,
        C (p.eval r / q.derivative.eval r) * (q /ₘ (X - C r)) := by
  have hqpos := hq.hasNonnegCoeffs.pos_leadingCoeff hpq.2.1.1
  rcases hpq.natDegree_eq_or_eq_succ with heq | hsucc
  · let a := p.leadingCoeff / q.leadingCoeff
    have hdeg : (p - C a * q).degree < q.natDegree :=
      degree_sub_c₀_mul_lt hpq.2.1.1 hpq.1.1 heq.symm hqpos
    have hlag := lagInterp_eq_g hpq.2.1.2 hqnd hqdeg hdeg
    have heval (r : ℝ) (hr : r ∈ q.roots.toFinset) :
        (p - C a * q).eval r = p.eval r := by
      simp only [eval_sub, eval_mul, eval_C,
        Polynomial.IsRoot.def.mp (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)),
        mul_zero, sub_zero]
    have hsum : lagInterp q (p - C a * q) = lagInterp q p := by
      simp only [lagInterp]
      exact Finset.sum_congr rfl fun r hr => by rw [heval r hr]
    refine ⟨a, div_nonneg (hp.hasNonnegCoeffs.pos_leadingCoeff hpq.1.1).le hqpos.le, ?_⟩
    change p = C a * q + lagInterp q p
    rw [← hsum, hlag]
    ring
  · refine ⟨0, le_rfl, ?_⟩
    have hdeg : p.degree < q.natDegree := by
      rw [degree_eq_natDegree hpq.1.1, hsucc]
      exact_mod_cast Nat.lt_succ_self p.natDegree
    simpa [lagInterp] using (lagInterp_eq_g hpq.2.1.2 hqnd hqdeg hdeg).symm

/-- Zero-aware three-member compatibility assembles a nonnegative right sum. -/
private lemma compatible_add_right {f g h : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hh : IsPFPolynomial h)
    (hfg : Compatible f g) (hfh : Compatible f h) (hgh : Compatible g h)
    {r : ℝ} (hr : 0 ≤ r) : Compatible f (g + C r * h) := by
  have hpair : PairwiseCompatible [f, g, h] := by
    apply pairwiseCompatible_of_forall_mem
    intro p hp q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    · exact Compatible.self_of_splits hf.splits
    · exact hfg
    · exact hfh
    · exact hfg.comm
    · exact Compatible.self_of_splits hg.splits
    · exact hgh
    · exact hfh.comm
    · exact hgh.comm
    · exact Compatible.self_of_splits hh.splits
  have hpf : ∀ p ∈ [f, g, h], IsPFPolynomial p := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hf
    · exact hg
    · exact hh
  simpa using (hpair.familyCompatible hpf).compatible_weightedSum
    (s := [(1, f)]) (t := [(1, g), (r, h)]) (by simp) (by simp) (by simp) (by simp [hr])

/-- Removing a root gives a positive-leading interlacer of the original polynomial. -/
private lemma cofactor_strictInterl {q : ℝ[X]} (hq : IsPFPolynomial q) (hq0 : q ≠ 0)
    {r : ℝ} (hr : r ∈ q.roots) : StrictInterl (q /ₘ (X - C r)) q := by
  have hfactor := mul_divByMonic_eq_iff_isRoot.mpr (isRoot_of_mem_roots hr)
  have hh := hq.of_X_sub_C_mul_factor hfactor.symm
  have hh0 : q /ₘ (X - C r) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hfactor
    exact hq0 hfactor.symm
  have h := (interlaces_one_linear (natDegree_X_sub_C r)).toStrictInterl.mul_common_factor
    hh0 hh.splits
  simpa only [mul_one, mul_comm, one_mul, hfactor] using h

/-- The successor and proportional tests make a cofactor image compatible with the full
right image. The three-member theorem permits all three images to vanish. -/
private lemma cofactor_image_compatible {N : ℕ} (A B : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hA : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (A p))
    (hB : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (B p))
    (hP : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → Compatible (A p) (B p))
    (hX : ∀ h, IsPFPolynomial h → h.natDegree < N → Compatible (A h) (B (X * h)))
    {q : ℝ[X]} (hq : IsPFPolynomial q) (hq0 : q ≠ 0) (hqN : q.natDegree ≤ N)
    {r : ℝ} (hr : r ∈ q.roots) : Compatible (A (q /ₘ (X - C r))) (B q) := by
  let H := q /ₘ (X - C r)
  have hfactor : (X - C r) * H = q :=
    mul_divByMonic_eq_iff_isRoot.mpr (isRoot_of_mem_roots hr)
  have hH := hq.of_X_sub_C_mul_factor hfactor.symm
  have hHN : H.natDegree < N := by
    dsimp [H]
    rw [natDegree_divByMonic_X_sub_C]
    have hqdeg := natDegree_pos_iff_degree_pos.mpr
      (degree_pos_of_root hq0 (isRoot_of_mem_roots hr))
    lia
  have hXH : (X * H).natDegree ≤ N :=
    natDegree_mul_le.trans (by simp only [natDegree_X]; lia)
  have hcompat := compatible_add_right (hA _ hH hHN.le) (hB _ hH.X_mul hXH)
    (hB _ hH hHN.le) (hX _ hH hHN) (hP _ hH hHN.le)
    (compatible_map B hB hH hH.X_mul hHN.le hXH
      (Compatible.self_X_mul_of_splits hH.splits)).comm
    (neg_nonneg.mpr (hq.roots_nonpos r hr))
  have heq : B (X * H) + C (-r) * B H = B q := by
    rw [← map_C_mul, ← map_add, ← hfactor]
    congr 1
    rw [map_neg]
    ring
  rwa [heq] at hcompat

/-- A PF-preserving map transports a common-right family; one further member can be added
when it is compatible with every image. -/
private lemma pairwise_mapped_with_right {N : ℕ} (A : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hA : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (A p))
    {q b : ℝ[X]} (hb : IsPFPolynomial b) {gs : List ℝ[X]}
    (hinput : ∀ f ∈ gs, IsPFPolynomial f ∧ f.natDegree ≤ N ∧ StrictInterl f q)
    (hAB : ∀ f ∈ gs, Compatible (A f) b) : PairwiseCompatible (b :: gs.map A) := by
  apply pairwiseCompatible_of_forall_mem
  intro f hf g hg
  rcases List.mem_cons.mp hf with rfl | hf
  · rcases List.mem_cons.mp hg with rfl | hg
    · exact Compatible.self_of_splits hb.splits
    · rcases List.mem_map.mp hg with ⟨v, hv, rfl⟩
      exact (hAB v hv).comm
  · rcases List.mem_map.mp hf with ⟨u, hu, rfl⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hAB u hu
    · rcases List.mem_map.mp hg with ⟨v, hv, rfl⟩
      obtain ⟨hfpf, hfN, hfq⟩ := hinput u hu
      obtain ⟨hgpf, hgN, hgq⟩ := hinput v hv
      exact compatible_map A hA hfpf hgpf hfN hgN
        (Compatible.of_commonInterleaver hfq hgq
          (hfpf.hasNonnegCoeffs.pos_leadingCoeff hfq.1.1)
          (hgpf.hasNonnegCoeffs.pos_leadingCoeff hgq.1.1))

/-- For a simple right input the residue expansion and compatibility suffice, including the
polynomial part in the equal-degree case. -/
private lemma row_of_right_nodup {N : ℕ} (A B : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hA : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (A p))
    (hB : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (B p))
    (hP : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → Compatible (A p) (B p))
    (hX : ∀ h, IsPFPolynomial h → h.natDegree < N → Compatible (A h) (B (X * h)))
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : StrictInterl p q) (hqN : q.natDegree ≤ N)
    (hqnd : q.roots.Nodup) (hqdeg : 1 ≤ q.natDegree) :
    IsPFPolynomial (A p + B q) := by
  classical
  let hs : List ℝ := q.roots.toFinset.toList
  let H (r : ℝ) := q /ₘ (X - C r)
  have hroot {r : ℝ} (hr : r ∈ hs) : r ∈ q.roots := by
    simpa [hs] using hr
  have hfactor {r : ℝ} (hr : r ∈ hs) : (X - C r) * H r = q :=
    mul_divByMonic_eq_iff_isRoot.mpr (isRoot_of_mem_roots (hroot hr))
  have hHpf {r : ℝ} (hr : r ∈ hs) : IsPFPolynomial (H r) :=
    hq.of_X_sub_C_mul_factor (hfactor hr).symm
  have hHdeg {r : ℝ} (hr : r ∈ hs) : (H r).natDegree < N := by
    dsimp [H]
    rw [natDegree_divByMonic_X_sub_C]
    have := degree_pos_of_root hpq.2.1.1 (isRoot_of_mem_roots (hroot hr))
    lia
  have hHinter {r : ℝ} (hr : r ∈ hs) : StrictInterl (H r) q :=
    cofactor_strictInterl hq hpq.2.1.1 (hroot hr)
  have hinput (f : ℝ[X]) (hf : f ∈ q :: hs.map H) :
      IsPFPolynomial f ∧ f.natDegree ≤ N ∧ StrictInterl f q := by
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨hq, hqN, StrictInterl.refl hpq.2.1.1 hpq.2.1.2⟩
    · rcases List.mem_map.mp hf with ⟨r, hr, rfl⟩
      exact ⟨hHpf hr, (hHdeg hr).le, hHinter hr⟩
  have hAB (f : ℝ[X]) (hf : f ∈ q :: hs.map H) : Compatible (A f) (B q) := by
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hP _ hq hqN
    · rcases List.mem_map.mp hf with ⟨r, hr, rfl⟩
      exact cofactor_image_compatible A B hA hB hP hX hq hpq.2.1.1 hqN (hroot hr)
  let fs := B q :: (q :: hs.map H).map A
  have hpf : ∀ f ∈ fs, IsPFPolynomial f := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hB q hq hqN
    · rcases List.mem_map.mp hf with ⟨g, hg, rfl⟩
      exact hA g (hinput g hg).1 (hinput g hg).2.1
  have hpair : PairwiseCompatible fs :=
    pairwise_mapped_with_right A hA (hB q hq hqN) hinput hAB
  obtain ⟨a, ha, hexpand⟩ := exists_cofactor_expansion hp hq hpq hqnd hqdeg
  let ws := (1, B q) :: (a, A q) :: hs.map fun r =>
    (p.eval r / q.derivative.eval r, A (H r))
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_cons] at hap
    rcases hap with rfl | rfl | hap
    · exact List.mem_cons_self
    · simp [fs]
    · rcases List.mem_map.mp hap with ⟨r, hr, rfl⟩
      simp only [fs, List.mem_cons, List.mem_map]
      exact Or.inr ⟨H r, Or.inr ⟨r, hr, rfl⟩, rfl⟩
  have hweights : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_cons] at hap
    rcases hap with rfl | rfl | hap
    · exact zero_le_one
    · exact ha
    · rcases List.mem_map.mp hap with ⟨r, hr, rfl⟩
      exact residue_nonneg_of_right_nodup hpq
        (hq.hasNonnegCoeffs.pos_leadingCoeff hpq.2.1.1)
        (hp.hasNonnegCoeffs.pos_leadingCoeff hpq.1.1) hqnd r (hroot hr)
  have hout := hpair.isPFPolynomial_weightedSum hpf hmem hweights
  have heq : weightedSum ws = A p + B q := by
    rw [hexpand, map_add, map_C_mul, map_sum]
    simp only [ws, weightedSum_cons, C_1, one_mul]
    rw [weightedSum_eq_sum_map]
    simp only [List.map_map, Function.comp_def, H]
    rw [Finset.sum_map_toList]
    simp only [map_C_mul]
    ring
  rwa [heq] at hout

/-- Constant input rows use the same-input compatibility at `1`. -/
private lemma row_of_natDegree_zero {N : ℕ} (A B : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hA : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (A p))
    (hB : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (B p))
    (hP : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → Compatible (A p) (B p))
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpdeg : p.natDegree = 0) (hqdeg : q.natDegree = 0) :
    IsPFPolynomial (A p + B q) := by
  have hone : (1 : ℝ[X]).natDegree ≤ N := by simp
  have hout := pf_combo (hA 1 IsPFPolynomial.one hone) (hB 1 IsPFPolynomial.one hone)
    (hP 1 IsPFPolynomial.one hone) (hp.hasNonnegCoeffs 0) (hq.hasNonnegCoeffs 0)
  have hmap (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (f : ℝ[X]) (hf : f.natDegree = 0) :
      T f = C (f.coeff 0) * T 1 := by
    conv_lhs => rw [eq_C_of_natDegree_eq_zero hf, ← mul_one (C (f.coeff 0))]
    exact map_C_mul T _ _
  rwa [← hmap A p hpdeg, ← hmap B q hqdeg] at hout

/-- Common derivative-shift regularization proves the row statement without simple-root
hypotheses, using coefficientwise continuity only on the input degree box. -/
private lemma row_of_commonInput {N : ℕ} (A B : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hA : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (A p))
    (hB : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (B p))
    (hP : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → Compatible (A p) (B p))
    (hX : ∀ h, IsPFPolynomial h → h.natDegree < N → Compatible (A h) (B (X * h)))
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) (hpN : p.natDegree ≤ N) (hqN : q.natDegree ≤ N) :
    IsPFPolynomial (A p + B q) := by
  rcases hpq with rfl | rfl | hpq
  · simpa using hB _ hq hqN
  · simpa using hA _ hp hpN
  by_cases hqdeg : q.natDegree = 0
  · have hpdeg : p.natDegree = 0 := by
      have := hpq.natDegree_eq_or_eq_succ
      lia
    exact row_of_natDegree_zero A B hA hB hP hp hq hpdeg hqdeg
  let eps : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have heps (n : ℕ) : 0 < eps n := by positivity
  let P : ℕ → ℝ[X] := fun n => iterateTDeriv (-(eps n)) N p
  let Q : ℕ → ℝ[X] := fun n => iterateTDeriv (-(eps n)) N q
  have hPF {f : ℝ[X]} (hf : IsPFPolynomial f) (n : ℕ) :
      IsPFPolynomial (iterateTDeriv (-(eps n)) N f) :=
    IsPFPolynomial.of_realRooted_nonneg
      (hf.hasNonnegCoeffs.iterateTDeriv_neg (heps n).le N)
      (splits_iterateTDeriv_all hf.splits _)
  have hPN (n : ℕ) : (P n).natDegree ≤ N := by simpa [P] using hpN
  have hQN (n : ℕ) : (Q n).natDegree ≤ N := by simpa [Q] using hqN
  have hout (n : ℕ) : IsPFPolynomial (A (P n) + B (Q n)) := by
    apply row_of_right_nodup A B hA hB hP hX (hPF hp n) (hPF hq n)
      (hpq.iterateTDeriv_common (-(eps n)) N) (hQN n)
    · exact (hasSimpleRoots_iterateTDeriv_neg_of_natDegree_le
        (heps n) hpq.2.1.1 hpq.2.1.2 hqN).roots_nodup
    · simp only [natDegree_iterateTDeriv]
      lia
  have hepslim : Tendsto (fun n => -(eps n)) atTop (𝓝 0) := by
    simpa [eps] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have hcoeff (f : ℝ[X]) (i : ℕ) :
      Tendsto (fun n => (iterateTDeriv (-(eps n)) N f).coeff i) atTop (𝓝 (f.coeff i)) := by
    simpa [Function.comp_def] using
      (continuousAt_coeff_iterateTDeriv_zero N f i).tendsto.comp hepslim
  have hAP := tendsto_coeff_linearMap_apply_of_coeff_tendsto A hPN (hcoeff p)
  have hBQ := tendsto_coeff_linearMap_apply_of_coeff_tendsto B hQN (hcoeff q)
  apply IsPFPolynomial.of_coeff_tendsto hout
  intro i
  simpa only [coeff_add] using (hAP i).add (hBQ i)

/-- A degree-bounded operator row preserves ordered PF pairs exactly when its positive
successor-input tests hold below the cap. At cap zero the tests are vacuous. -/
theorem row_preserves_iff_commonInputUpTo (N : ℕ) (A B : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hA : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (A p))
    (hB : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (B p))
    (hP : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → Compatible (A p) (B p)) :
    (∀ p q, IsPFPolynomial p → IsPFPolynomial q → Interl p q →
      p.natDegree ≤ N → q.natDegree ≤ N → IsPFPolynomial (A p + B q)) ↔
    ∀ h, IsPFPolynomial h → h.natDegree < N →
      ∀ r : ℝ, 0 < r → IsPFPolynomial (C r * A h + B (X * h)) := by
  constructor
  · intro hrow h hh hhN r hr
    have hself : Interl h (X * h) := by
      by_cases hh0 : h = 0
      · simp [hh0, interl_zero_left]
      · exact (strictInterl_self_X_mul_of_nonneg hh0 hh.splits hh.hasNonnegCoeffs).toInterl
    have hXh : (X * h).natDegree ≤ N :=
      natDegree_mul_le.trans (by simp only [natDegree_X]; lia)
    simpa only [map_C_mul] using hrow (C r * h) (X * h)
      (hh.const_mul hr) hh.X_mul (hself.C_mul_left_of_nonneg hr.le)
      ((natDegree_C_mul_le _ _).trans hhN.le) hXh
  · intro hX p q hp hq hpq hpN hqN
    apply row_of_commonInput A B hA hB hP _ hp hq hpq hpN hqN
    intro h hh hhN
    exact compatible_of_pf_pos (hA h hh hhN.le)
      (hB _ hh.X_mul (natDegree_mul_le.trans (by simp only [natDegree_X]; lia)))
      (hX h hh hhN)

/-- The unrestricted row reduction for arbitrary real-linear entries. -/
theorem row_preserves_iff_commonInput (A B : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hA : ∀ p, IsPFPolynomial p → IsPFPolynomial (A p))
    (hB : ∀ p, IsPFPolynomial p → IsPFPolynomial (B p))
    (hP : ∀ p, IsPFPolynomial p → Compatible (A p) (B p)) :
    (∀ p q, IsPFPolynomial p → IsPFPolynomial q → Interl p q →
      IsPFPolynomial (A p + B q)) ↔
    ∀ h, IsPFPolynomial h → ∀ r : ℝ, 0 < r →
      IsPFPolynomial (C r * A h + B (X * h)) := by
  constructor
  · intro hrow h hh
    exact (row_preserves_iff_commonInputUpTo (h.natDegree + 1) A B
      (fun p hp _ => hA p hp) (fun p hp _ => hB p hp) (fun p hp _ => hP p hp)).mp
        (fun p q hp hq hpq _ _ => hrow p q hp hq hpq) h hh (by lia)
  · intro hX p q hp hq hpq
    exact (row_preserves_iff_commonInputUpTo (max p.natDegree q.natDegree) A B
      (fun p hp _ => hA p hp) (fun p hp _ => hB p hp) (fun p hp _ => hP p hp)).mpr
        (fun h hh _ => hX h hh) p q hp hq hpq (le_max_left _ _) (le_max_right _ _)

/-- Compatibility form of the bounded row reduction, with the successor test strictly below
the input cap and no restriction on output degrees. -/
theorem row_preserves_iff_compatibleUpTo (N : ℕ) (A B : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hA : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (A p))
    (hB : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → IsPFPolynomial (B p))
    (hP : ∀ p, IsPFPolynomial p → p.natDegree ≤ N → Compatible (A p) (B p)) :
    (∀ p q, IsPFPolynomial p → IsPFPolynomial q → Interl p q →
      p.natDegree ≤ N → q.natDegree ≤ N → IsPFPolynomial (A p + B q)) ↔
    ∀ h, IsPFPolynomial h → h.natDegree < N → Compatible (A h) (B (X * h)) := by
  rw [row_preserves_iff_commonInputUpTo N A B hA hB hP]
  constructor
  · intro hX h hh hhN
    apply (compatible_iff_isPFPolynomial_pos (hA h hh hhN.le)
      (hB _ hh.X_mul (natDegree_mul_le.trans (by simp only [natDegree_X]; lia)))).mpr
    exact hX h hh hhN
  · intro hX h hh hhN r hr
    exact (compatible_iff_isPFPolynomial_pos (hA h hh hhN.le)
      (hB _ hh.X_mul (natDegree_mul_le.trans (by simp only [natDegree_X]; lia)))).mp
      (hX h hh hhN) r hr

/-- Compatibility form of the unrestricted row reduction. -/
theorem row_preserves_iff_compatible (A B : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hA : ∀ p, IsPFPolynomial p → IsPFPolynomial (A p))
    (hB : ∀ p, IsPFPolynomial p → IsPFPolynomial (B p))
    (hP : ∀ p, IsPFPolynomial p → Compatible (A p) (B p)) :
    (∀ p q, IsPFPolynomial p → IsPFPolynomial q → Interl p q →
      IsPFPolynomial (A p + B q)) ↔
    ∀ h, IsPFPolynomial h → Compatible (A h) (B (X * h)) := by
  rw [row_preserves_iff_commonInput A B hA hB hP]
  constructor
  · intro hX h hh
    exact (compatible_iff_isPFPolynomial_pos (hA h hh) (hB _ hh.X_mul)).mpr (hX h hh)
  · intro hX h hh
    exact (compatible_iff_isPFPolynomial_pos (hA h hh) (hB _ hh.X_mul)).mp (hX h hh)

/-- At input cap zero same-input compatibility alone discharges every ordered row. -/
theorem row_preservesUpTo_zero (A B : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hA : ∀ p, IsPFPolynomial p → p.natDegree ≤ 0 → IsPFPolynomial (A p))
    (hB : ∀ p, IsPFPolynomial p → p.natDegree ≤ 0 → IsPFPolynomial (B p))
    (hP : ∀ p, IsPFPolynomial p → p.natDegree ≤ 0 → Compatible (A p) (B p)) :
    ∀ p q, IsPFPolynomial p → IsPFPolynomial q → Interl p q →
      p.natDegree ≤ 0 → q.natDegree ≤ 0 → IsPFPolynomial (A p + B q) := by
  apply (row_preserves_iff_commonInputUpTo 0 A B hA hB hP).mpr
  intro h _ hhN
  exact (Nat.not_lt_zero _ hhN).elim

end RealRooted.OperatorMatrix
