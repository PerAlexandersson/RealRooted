module

public import Mathlib

/-!
# Positive unimodular polynomial Gram matrices

This file proves that an everywhere positive-definite symmetric matrix over `ℝ[X]` whose
determinant is a unit is polynomially congruent to the identity.  The proof is by descent on the
sum of the degrees of the diagonal entries.
-/

@[expose] public section

noncomputable section

open Filter Matrix Polynomial Topology
open scoped BigOperators Matrix MatrixOrder

namespace Polynomial

/-- A nonzero real polynomial which is nonnegative on the real line has nonnegative leading
coefficient. -/
theorem leadingCoeff_nonneg_of_eval_nonneg {p : ℝ[X]} (hp : p ≠ 0)
    (h : ∀ x : ℝ, 0 ≤ p.eval x) : 0 ≤ p.leadingCoeff := by
  by_cases hd : p.natDegree = 0
  · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hd
    simpa only [leadingCoeff_C, eval_C] using h 0
  by_contra hn
  have hnat : 0 < p.natDegree := Nat.pos_of_ne_zero hd
  have ht : Tendsto p.eval atTop atBot :=
    p.tendsto_atBot_of_leadingCoeff_nonpos
      (natDegree_pos_iff_degree_pos.mp hnat) (le_of_not_ge hn)
  obtain ⟨x, hx⟩ := (ht.eventually_lt_atBot 0).exists
  exact (not_lt_of_ge (h x)) hx

/-- A nonzero real polynomial which is nonnegative on the real line has positive leading
coefficient. -/
theorem leadingCoeff_pos_of_eval_nonneg {p : ℝ[X]} (hp : p ≠ 0)
    (h : ∀ x : ℝ, 0 ≤ p.eval x) : 0 < p.leadingCoeff := by
  exact lt_of_le_of_ne (leadingCoeff_nonneg_of_eval_nonneg hp h)
    (Ne.symm (leadingCoeff_ne_zero.mpr hp))

/-- A nonzero real polynomial which is positive on the real line has positive leading
coefficient. -/
theorem leadingCoeff_pos_of_eval_pos {p : ℝ[X]} (h : ∀ x : ℝ, 0 < p.eval x) :
    0 < p.leadingCoeff := by
  have hp : p ≠ 0 := by
    intro hp
    simpa only [hp, eval_zero, lt_self_iff_false] using h 0
  exact lt_of_le_of_ne (leadingCoeff_nonneg_of_eval_nonneg hp fun x => (h x).le)
    (Ne.symm (leadingCoeff_ne_zero.mpr hp))

/-- A nonzero real polynomial which is nonnegative on the real line has even natural degree. -/
theorem even_natDegree_of_eval_nonneg {p : ℝ[X]} (hp : p ≠ 0)
    (h : ∀ x : ℝ, 0 ≤ p.eval x) : Even p.natDegree := by
  have hlead : 0 < p.leadingCoeff := leadingCoeff_pos_of_eval_nonneg hp h
  have hcomp_ne : p.comp (-X) ≠ 0 := comp_neg_X_eq_zero_iff.not.mpr hp
  have hcomp : ∀ x : ℝ, 0 ≤ (p.comp (-X)).eval x := by
    intro x
    simpa only [eval_comp, eval_neg, eval_X] using h (-x)
  have hcomp_lead : 0 < (p.comp (-X)).leadingCoeff :=
    leadingCoeff_pos_of_eval_nonneg hcomp_ne hcomp
  rw [comp_neg_X_leadingCoeff_eq] at hcomp_lead
  rcases p.natDegree.even_or_odd with he | ho
  · exact he
  · rw [ho.neg_one_pow] at hcomp_lead
    norm_num at hcomp_lead
    exact ((not_lt_of_ge hlead.le) hcomp_lead).elim

/-- A real polynomial which is positive on the real line has even natural degree. -/
theorem even_natDegree_of_eval_pos {p : ℝ[X]} (h : ∀ x : ℝ, 0 < p.eval x) :
    Even p.natDegree := by
  have hp : 0 < p.leadingCoeff := leadingCoeff_pos_of_eval_pos h
  have hcomp : ∀ x : ℝ, 0 < (p.comp (-X)).eval x := by
    intro x
    simpa only [eval_comp, eval_neg, eval_X] using h (-x)
  have hc : 0 < (p.comp (-X)).leadingCoeff := leadingCoeff_pos_of_eval_pos hcomp
  rw [comp_neg_X_leadingCoeff_eq] at hc
  rcases p.natDegree.even_or_odd with he | ho
  · exact he
  · rw [ho.neg_one_pow] at hc
    norm_num at hc
    exact ((not_lt_of_ge hp.le) hc).elim

/-- The off-diagonal degree estimate used for positive polynomial Gram matrices. -/
theorem two_mul_natDegree_le_of_sq_eval_le_mul_eval {f g h : ℝ[X]}
    (hf : ∀ x : ℝ, 0 < f.eval x) (hh : ∀ x : ℝ, 0 < h.eval x)
    (hbound : ∀ x : ℝ, (g.eval x) ^ 2 ≤ f.eval x * h.eval x) :
    2 * g.natDegree ≤ f.natDegree + h.natDegree := by
  by_cases hg : g = 0
  · simp only [hg, natDegree_zero, mul_zero, zero_le]
  have hf0 : f ≠ 0 := by
    intro hzero
    simpa only [hzero, eval_zero, lt_self_iff_false] using hf 0
  have hh0 : h ≠ 0 := by
    intro hzero
    simpa only [hzero, eval_zero, lt_self_iff_false] using hh 0
  by_contra hn
  have hlt : (f * h).natDegree < (g ^ 2).natDegree := by
    rw [natDegree_mul hf0 hh0, natDegree_pow]
    simpa only [Nat.not_le] using hn
  have hq_ne : f * h - g ^ 2 ≠ 0 := by
    intro heq
    have := congrArg natDegree heq
    rw [natDegree_zero] at this
    have hgdeg : 0 < (g ^ 2).natDegree := (Nat.zero_le _).trans_lt hlt
    have hdeg := natDegree_sub_eq_right_of_natDegree_lt hlt
    rw [heq, natDegree_zero] at hdeg
    exact (Nat.ne_of_gt hgdeg) hdeg.symm
  have hq_eval : ∀ x : ℝ, 0 ≤ (f * h - g ^ 2).eval x := by
    intro x
    simpa only [eval_sub, eval_mul, eval_pow] using sub_nonneg.mpr (hbound x)
  have hq_lc := leadingCoeff_nonneg_of_eval_nonneg hq_ne hq_eval
  have hdeg := natDegree_sub_eq_right_of_natDegree_lt hlt
  have hcoeff : (f * h - g ^ 2).leadingCoeff = -(g.leadingCoeff ^ 2) := by
    rw [leadingCoeff, hdeg, coeff_sub, coeff_eq_zero_of_natDegree_lt hlt,
      natDegree_pow, two_mul, pow_two, coeff_mul_degree_add_degree, zero_sub]
    ring
  rw [hcoeff] at hq_lc
  exact (not_lt_of_ge hq_lc) (neg_neg_of_pos (sq_pos_of_ne_zero (leadingCoeff_ne_zero.mpr hg)))

end Polynomial

namespace Polynomial

private theorem coeff_prod_at_sum_of_natDegree_le {R ι : Type*} [CommRing R]
    (s : Finset ι) (f : ι → R[X]) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (s.prod f).coeff (s.sum d) = s.prod fun i => (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hs : ∀ i ∈ s, (f i).natDegree ≤ d i :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hsdeg : (s.prod f).natDegree ≤ s.sum d := by
        refine (natDegree_prod_le s f).trans ?_
        exact Finset.sum_le_sum hs
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        coeff_mul_add_eq_of_natDegree_le (h a (Finset.mem_insert_self a s)) hsdeg,
        ih hs, Finset.prod_insert ha]

end Polynomial

namespace Matrix

/-- The coefficient of the determinant at the sum of row and column degree bounds is the
determinant of the matrix of coefficients at the corresponding entrywise bounds. -/
theorem coeff_det_eq_det_coeff_of_natDegree_le {R n : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] (M : Matrix n n R[X]) (r c : n → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ r i + c j) :
    M.det.coeff ((∑ i, r i) + ∑ j, c j) =
      (of fun i j => (M i j).coeff (r i + c j)).det := by
  classical
  rw [det_apply' M, det_apply' (of fun i j => (M i j).coeff (r i + c j))]
  change Polynomial.lcoeff R ((∑ i, r i) + ∑ j, c j)
      (∑ σ : Equiv.Perm n,
        ((Equiv.Perm.sign σ : ℤ) : R[X]) * ∏ i, M (σ i) i) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, coeff_intCast_mul]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [of_apply]
  congr 1
  have hsum : (∑ i : n, (r (σ i) + c i)) =
      (∑ i : n, r i) + (∑ i : n, c i) := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ r]
  rw [← hsum, Polynomial.coeff_prod_at_sum_of_natDegree_le]
  exact fun i _ => hM (σ i) i

end Matrix

namespace Matrix

private theorem PosDef.apply_sq_le_mul_apply_diag {n : Type*}
    {A : Matrix n n ℝ} (hA : A.PosDef) (i j : n) :
    (A i j) ^ 2 ≤ A i i * A j j := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [pow_two, le_refl]
  let e : Fin 2 → n := ![i, j]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e]
  have hdet := (hA.submatrix he).posSemidef.det_nonneg
  have hsym := hA.isHermitian.eq
  rw [det_fin_two] at hdet
  simp only [submatrix_apply, e, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  have hji : A j i = A i j := by
    simpa only [conjTranspose_eq_transpose_of_trivial, transpose_apply] using
      (congrFun (congrFun hsym j) i).symm
  rw [hji, sub_nonneg] at hdet
  simpa only [pow_two] using hdet

private theorem eval_congr_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {G E : Matrix n n ℝ[X]} (hG : ∀ x : ℝ, (G.map (evalRingHom x)).PosDef)
    (hE : IsUnit E.det) :
    ∀ x : ℝ, ((Eᵀ * G * E).map (evalRingHom x)).PosDef := by
  intro x
  have hmap_unit : IsUnit (E.map (evalRingHom x)) := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ?_)
    change ((evalRingHom x).mapMatrix E).det ≠ 0
    simpa only [RingHom.map_det] using (hE.map (evalRingHom x)).ne_zero
  have hinj : Function.Injective (E.map (evalRingHom x)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hmap_unit
  simpa only [Matrix.map_mul, transpose_map, conjTranspose_eq_transpose_of_trivial] using
    (hG x).conjTranspose_mul_mul_same hinj

private theorem transpose_mul_mul_self_isSymm {R n : Type*} [CommRing R]
    [Fintype n] {G E : Matrix n n R} (hG : Gᵀ = G) :
    (Eᵀ * G * E)ᵀ = Eᵀ * G * E := by
  simp only [transpose_mul, transpose_transpose, hG]
  rw [Matrix.mul_assoc]

-- Ported from Tau Ceti's Apache-2.0-licensed matrix positive-definiteness utilities.
private theorem isOpen_setOf_forall_dotProduct_mulVec_pos {n : Type*} [Fintype n] :
    IsOpen {M : Matrix n n ℝ | ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x} := by
  rw [isOpen_iff_mem_nhds]
  intro M hM
  have key : ∀ᶠ N in nhds M,
      ∀ x ∈ Metric.sphere (0 : n → ℝ) 1, 0 < x ⬝ᵥ N *ᵥ x := by
    refine (isCompact_sphere (0 : n → ℝ) 1).eventually_forall_of_forall_eventually
      fun y hy => ?_
    rw [mem_sphere_zero_iff_norm] at hy
    have hy0 : y ≠ 0 := norm_ne_zero_iff.1 (hy ▸ one_ne_zero)
    have hcont : Continuous fun z : Matrix n n ℝ × (n → ℝ) => z.2 ⬝ᵥ z.1 *ᵥ z.2 := by
      fun_prop
    exact (isOpen_lt continuous_const hcont).mem_nhds (hM y hy0)
  filter_upwards [key] with N hN x hx
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : n → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0]
  have hscale : x ⬝ᵥ N *ᵥ x =
      ‖x‖ ^ 2 * ((‖x‖⁻¹ • x) ⬝ᵥ N *ᵥ (‖x‖⁻¹ • x)) := by
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, sq]
    field_simp
  rw [hscale]
  exact mul_pos (pow_pos (norm_pos_iff.2 hx) 2) (hN _ hmem)

/-- A continuous nonsingular symmetric family of real matrices which is positive definite at one
point is positive definite everywhere on the real line. -/
theorem posDef_of_continuous_of_det_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℝ) (hA : Continuous A) (hAsymm : ∀ x, (A x)ᵀ = A x)
    (hdet : ∀ x, (A x).det ≠ 0) {x₀ : ℝ} (hx₀ : (A x₀).PosDef) :
    ∀ x, (A x).PosDef := by
  let S : Set ℝ := {x | ∀ v : n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ A x *ᵥ v}
  have hopen : IsOpen S := isOpen_setOf_forall_dotProduct_mulVec_pos.preimage hA
  have hS : S = {x | (A x).PosSemidef} := by
    ext x
    constructor
    · intro hx
      change ∀ v : n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ A x *ᵥ v at hx
      exact (posDef_iff_dotProduct_mulVec.mpr
        ⟨isHermitian_iff_isSymm.mpr (hAsymm x), by
          simpa only [star_trivial] using hx⟩).posSemidef
    · intro hx
      exact (posDef_iff_dotProduct_mulVec.mp
        (hx.posDef_iff_det_ne_zero.mpr (hdet x))).2
  have hclosed : IsClosed S := by
    rw [hS]
    exact posSemidef_is_closed.preimage hA
  have hclopen : IsClopen S := ⟨hclosed, hopen⟩
  have hx₀S : x₀ ∈ S := by
    change ∀ v : n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ A x₀ *ᵥ v
    simpa only [star_trivial] using (posDef_iff_dotProduct_mulVec.mp hx₀).2
  have hSuniv : S = Set.univ := hclopen.eq_univ ⟨x₀, hx₀S⟩
  intro x
  apply posDef_iff_dotProduct_mulVec.mpr
  refine ⟨isHermitian_iff_isSymm.mpr (hAsymm x), ?_⟩
  intro v hv
  have hx : x ∈ S := by rw [hSuniv]; exact Set.mem_univ x
  simpa only [S, star_trivial] using hx v hv

private theorem exists_real_transpose_mul_mul_eq_one_of_posDef {n : Type*}
    [Fintype n] [DecidableEq n] {H : Matrix n n ℝ} (hH : H.PosDef) :
    ∃ R : Matrix n n ℝ, IsUnit R.det ∧ Rᵀ * H * R = 1 := by
  have hstrict : IsStrictlyPositive H := hH.isStrictlyPositive
  obtain ⟨S, hSunit, hSself, hfactor⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self.mp
      hstrict
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSunit
  refine ⟨S⁻¹, S.isUnit_nonsing_inv_det hSdet, ?_⟩
  have hST : Sᵀ = S := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      hSself.star_eq
  rw [transpose_nonsing_inv, hST, hfactor]
  simp only [← Matrix.mul_assoc, S.nonsing_inv_mul hSdet, one_mul,
    S.mul_nonsing_inv hSdet]

private def diagDegreeSum {n : Type*} [Fintype n] (G : Matrix n n ℝ[X]) : ℕ :=
  ∑ i, (G i i).natDegree

private theorem exists_transpose_mul_mul_eq_one_of_diagDegreeSum_eq_zero {n : Type*}
    [Fintype n] [DecidableEq n] {G : Matrix n n ℝ[X]}
    (hzero : diagDegreeSum G = 0)
    (hpos : ∀ x : ℝ, (G.map (evalRingHom x)).PosDef) :
    ∃ Q : Matrix n n ℝ[X], IsUnit Q.det ∧ Qᵀ * G * Q = 1 := by
  have hdiag_zero (i : n) : (G i i).natDegree = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hzero i
      (Finset.mem_univ i)
  have hdiag_pos (i : n) (x : ℝ) : 0 < (G i i).eval x := by
    simpa only [map_apply, coe_evalRingHom] using (hpos x).diag_pos (i := i)
  have hentry_zero (i j : n) : (G i j).natDegree = 0 := by
    have hcross (x : ℝ) : ((G i j).eval x) ^ 2 ≤
        (G i i).eval x * (G j j).eval x := by
      simpa only [map_apply, coe_evalRingHom] using
        (hpos x).apply_sq_le_mul_apply_diag i j
    have hle := Polynomial.two_mul_natDegree_le_of_sq_eval_le_mul_eval
      (hdiag_pos i) (hdiag_pos j) hcross
    rw [hdiag_zero i, hdiag_zero j, add_zero] at hle
    lia
  let H : Matrix n n ℝ := fun i j => (G i j).coeff 0
  have hGH : G = H.map C := by
    apply Matrix.ext
    intro i j
    change G i j = C ((G i j).coeff 0)
    exact eq_C_of_natDegree_eq_zero (hentry_zero i j)
  have hHpos : H.PosDef := by
    have h0 := hpos 0
    rw [hGH] at h0
    have heval : (H.map C).map (evalRingHom 0) = H := by
      ext i j
      simp only [map_apply, coe_evalRingHom, eval_C]
    rw [heval] at h0
    exact h0
  obtain ⟨R, hRdet, hR⟩ := exists_real_transpose_mul_mul_eq_one_of_posDef hHpos
  refine ⟨R.map C, ?_, ?_⟩
  · change IsUnit (C.mapMatrix R).det
    simpa only [RingHom.map_det] using hRdet.map C
  · rw [hGH]
    have hmap := congrArg C.mapMatrix hR
    change (C.mapMatrix R)ᵀ * C.mapMatrix H * C.mapMatrix R = 1
    convert hmap using 1
    · ext i j
      simp [Matrix.mul_apply]
    · apply Matrix.ext
      intro i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]

private theorem exists_congr_diagDegreeSum_lt {n : Type*} [Fintype n] [DecidableEq n]
    {G : Matrix n n ℝ[X]} (hGdet : IsUnit G.det)
    (hGpos : ∀ x : ℝ, (G.map (evalRingHom x)).PosDef)
    (hmu : 0 < diagDegreeSum G) :
    ∃ E : Matrix n n ℝ[X], IsUnit E.det ∧
      diagDegreeSum (Eᵀ * G * E) < diagDegreeSum G := by
  have hdiag_pos (i : n) (x : ℝ) : 0 < (G i i).eval x := by
    simpa only [map_apply, coe_evalRingHom] using (hGpos x).diag_pos (i := i)
  let d : n → ℕ := fun i => (G i i).natDegree / 2
  have hdiag_degree (i : n) : (G i i).natDegree = 2 * d i := by
    change (G i i).natDegree = 2 * ((G i i).natDegree / 2)
    exact (Nat.two_mul_div_two_of_even
      (Polynomial.even_natDegree_of_eval_pos (hdiag_pos i))).symm
  have hentry_degree (i j : n) : (G i j).natDegree ≤ d i + d j := by
    have hcross (x : ℝ) : ((G i j).eval x) ^ 2 ≤
        (G i i).eval x * (G j j).eval x := by
      simpa only [map_apply, coe_evalRingHom] using
        (hGpos x).apply_sq_le_mul_apply_diag i j
    have hle := Polynomial.two_mul_natDegree_le_of_sq_eval_le_mul_eval
      (hdiag_pos i) (hdiag_pos j) hcross
    rw [hdiag_degree i, hdiag_degree j] at hle
    lia
  let D : ℕ := ∑ i, d i
  have hmu_eq : diagDegreeSum G = 2 * D := by
    change (∑ i, (G i i).natDegree) = 2 * ∑ i, d i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact hdiag_degree i
  have hD : 0 < D := by lia
  let L : Matrix n n ℝ := fun i j => (G i j).coeff (d i + d j)
  have hLdet : L.det = 0 := by
    have hcoeff := coeff_det_eq_det_coeff_of_natDegree_le G d d hentry_degree
    change G.det.coeff (D + D) = L.det at hcoeff
    rw [coeff_eq_zero_of_natDegree_lt] at hcoeff
    · exact hcoeff.symm
    · rw [natDegree_eq_zero_of_isUnit hGdet]
      lia
  obtain ⟨a, ha_ne, haL⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hLdet
  let s : Finset n := Finset.univ.filter fun i => a i ≠ 0
  have hs : s.Nonempty := by
    by_contra hs0
    apply ha_ne
    funext i
    change a i = 0
    have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs0
    have hi : i ∉ s := by rw [hempty]; exact Finset.notMem_empty i
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image s d hs
  have haj : a j ≠ 0 := by simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  have hmax (i : n) (hai : a i ≠ 0) : d i ≤ d j := by
    exact hjmax i (by simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and])
  let v : n → ℝ[X] := fun i => C (a i) * X ^ (d j - d i)
  let E : Matrix n n ℝ[X] := (1 : Matrix n n ℝ[X]).updateCol j v
  have hvj : v j = C (a j) := by simp only [v, Nat.sub_self, pow_zero, mul_one]
  have hEdet : E.det = C (a j) := by
    have hcol : (fun k => ∑ i, v i • (1 : Matrix n n ℝ[X]) k i) = v := by
      funext k
      rw [Fintype.sum_eq_single k]
      · simp
      · intro i hik
        simp only [Matrix.one_apply, smul_ite, smul_zero, ite_eq_right_iff]
        exact fun hki => (hik hki.symm).elim
    calc
      E.det = ((1 : Matrix n n ℝ[X]).updateCol j
          (fun k => ∑ i, v i • (1 : Matrix n n ℝ[X]) k i)).det := by rw [hcol]
      _ = v j • (1 : Matrix n n ℝ[X]).det := det_updateCol_sum _ _ _
      _ = C (a j) := by simp only [det_one, smul_eq_mul, mul_one, hvj]
  have hEunit : IsUnit E.det := by
    rw [hEdet]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr haj)
  refine ⟨E, hEunit, ?_⟩
  let G' : Matrix n n ℝ[X] := Eᵀ * G * E
  have hone_right (f : n → ℝ[X]) (i : n) :
      (∑ k, f k * (1 : Matrix n n ℝ[X]) k i) = f i := by
    rw [Fintype.sum_eq_single i]
    · simp
    · intro k hki
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
      exact fun hik => (hki hik).elim
  have hone_left (f : n → ℝ[X]) (i : n) :
      (∑ k, (1 : Matrix n n ℝ[X]) k i * f k) = f i := by
    rw [Fintype.sum_eq_single i]
    · simp
    · intro k hki
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, ite_eq_right_iff]
      exact fun hik => (hki hik).elim
  have hdiag_same (i : n) (hij : i ≠ j) : G' i i = G i i := by
    simp only [G', E, Matrix.mul_apply, transpose_apply, updateCol_apply, ite_eq_right hij]
    rw [hone_right, hone_left]
  have hdiag_changed : G' j j = ∑ i, ∑ k, v i * G i k * v k := by
    simp only [G', E, Matrix.mul_apply, transpose_apply, updateCol_apply]
    simp only [ite_true, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hterm_degree (i k : n) :
      (v i * G i k * v k).natDegree ≤ 2 * d j := by
    by_cases hai : a i = 0
    · simp only [v, hai, map_zero, zero_mul, natDegree_zero, zero_le]
    by_cases hak : a k = 0
    · simp only [v, hak, map_zero, zero_mul, mul_zero, natDegree_zero, zero_le]
    have hi := hmax i hai
    have hk := hmax k hak
    have hvi : (v i).natDegree ≤ d j - d i := by
      change (C (a i) * X ^ (d j - d i)).natDegree ≤ d j - d i
      calc
        _ ≤ (C (a i)).natDegree + (X ^ (d j - d i)).natDegree := natDegree_mul_le
        _ = d j - d i := by simp
    have hvk : (v k).natDegree ≤ d j - d k := by
      change (C (a k) * X ^ (d j - d k)).natDegree ≤ d j - d k
      calc
        _ ≤ (C (a k)).natDegree + (X ^ (d j - d k)).natDegree := natDegree_mul_le
        _ = d j - d k := by simp
    calc
      (v i * G i k * v k).natDegree
          ≤ (v i * G i k).natDegree + (v k).natDegree := natDegree_mul_le
      _ ≤ ((v i).natDegree + (G i k).natDegree) + (v k).natDegree :=
        Nat.add_le_add_right natDegree_mul_le _
      _ ≤ ((d j - d i) + (d i + d k)) + (d j - d k) :=
        Nat.add_le_add (Nat.add_le_add hvi (hentry_degree i k)) hvk
      _ = ((d j - d i) + d i) + ((d j - d k) + d k) := by ac_rfl
      _ = d j + d j := by rw [Nat.sub_add_cancel hi, Nat.sub_add_cancel hk]
      _ = 2 * d j := by rw [two_mul]
  have hchanged_degree : (G' j j).natDegree ≤ 2 * d j := by
    rw [hdiag_changed]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    exact hterm_degree i k
  have hterm_coeff (i k : n) :
      (v i * G i k * v k).coeff (2 * d j) = a i * L i k * a k := by
    by_cases hai : a i = 0
    · simp only [v, hai, map_zero, zero_mul, coeff_zero]
    by_cases hak : a k = 0
    · simp only [v, hak, map_zero, zero_mul, mul_zero, coeff_zero]
    have hi := hmax i hai
    have hk := hmax k hak
    have hsum : 2 * d j = (d i + d k) + ((d j - d i) + (d j - d k)) := by
      calc
        2 * d j = d j + d j := two_mul (d j)
        _ = ((d j - d i) + d i) + ((d j - d k) + d k) := by
          rw [Nat.sub_add_cancel hi, Nat.sub_add_cancel hk]
        _ = (d i + d k) + ((d j - d i) + (d j - d k)) := by ac_rfl
    have hpoly : v i * G i k * v k =
        C (a i * a k) * G i k * X ^ ((d j - d i) + (d j - d k)) := by
      simp only [v, map_mul]
      rw [pow_add]
      ring
    rw [hpoly, hsum, coeff_mul_X_pow, coeff_C_mul]
    change (a i * a k) * L i k = a i * L i k * a k
    ring
  have hkernel (i : n) : ∑ k, L i k * a k = 0 := by
    have hi := congrFun haL i
    simpa only [mulVec, dotProduct, Pi.zero_apply] using hi
  have hchanged_coeff : (G' j j).coeff (2 * d j) = 0 := by
    rw [hdiag_changed, finsetSum_coeff]
    simp_rw [finsetSum_coeff, hterm_coeff]
    calc
      ∑ i, ∑ k, a i * L i k * a k = ∑ i, a i * (∑ k, L i k * a k) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = 0 := by simp only [hkernel, mul_zero, Finset.sum_const_zero]
  have hG'pos : ∀ x : ℝ, (G'.map (evalRingHom x)).PosDef := by
    simpa only [G'] using eval_congr_posDef hGpos hEunit
  have hchanged_ne : G' j j ≠ 0 := by
    intro hzero
    have hpos := (hG'pos 0).diag_pos (i := j)
    simp only [map_apply, coe_evalRingHom, hzero, eval_zero, lt_self_iff_false] at hpos
  have hchanged_lt : (G' j j).natDegree < 2 * d j := by
    apply lt_of_le_of_ne hchanged_degree
    intro heq
    have hlead := leadingCoeff_ne_zero.mpr hchanged_ne
    rw [leadingCoeff, heq, hchanged_coeff] at hlead
    exact hlead rfl
  change (∑ i, (G' i i).natDegree) < ∑ i, (G i i).natDegree
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hij : i = j
    · subst i
      rw [hdiag_degree j]
      exact hchanged_lt.le
    · rw [hdiag_same i hij]
  · exact ⟨j, Finset.mem_univ j, by rw [hdiag_degree j]; exact hchanged_lt⟩

/-- An everywhere positive-definite symmetric polynomial matrix with unit determinant is
polynomially congruent to the identity. -/
theorem exists_transpose_mul_mul_eq_one_of_posDef_eval {n : Type*}
    [Fintype n] [DecidableEq n] {G : Matrix n n ℝ[X]} (hGsymm : Gᵀ = G)
    (hGdet : IsUnit G.det) (hGpos : ∀ x : ℝ, (G.map (evalRingHom x)).PosDef) :
    ∃ Q : Matrix n n ℝ[X], IsUnit Q.det ∧ Qᵀ * G * Q = 1 := by
  generalize hmu : diagDegreeSum G = mu
  induction mu using Nat.strong_induction_on generalizing G with
  | h mu ih =>
      by_cases hzero : mu = 0
      · apply exists_transpose_mul_mul_eq_one_of_diagDegreeSum_eq_zero
        · rw [hmu, hzero]
        · exact hGpos
      · have hmupos : 0 < diagDegreeSum G := by rw [hmu]; exact Nat.pos_of_ne_zero hzero
        obtain ⟨E, hEdet, hdrop⟩ := exists_congr_diagDegreeSum_lt hGdet hGpos hmupos
        let G' : Matrix n n ℝ[X] := Eᵀ * G * E
        have hG'symm : G'ᵀ = G' := by
          exact transpose_mul_mul_self_isSymm hGsymm
        have hG'det : IsUnit G'.det := by
          change IsUnit (Eᵀ * G * E).det
          rw [det_mul, det_mul, det_transpose]
          exact (hEdet.mul hGdet).mul hEdet
        have hG'pos : ∀ x : ℝ, (G'.map (evalRingHom x)).PosDef := by
          exact eval_congr_posDef hGpos hEdet
        obtain ⟨V, hVdet, hV⟩ := ih (diagDegreeSum G') (by rw [← hmu]; exact hdrop)
          hG'symm hG'det hG'pos rfl
        refine ⟨E * V, ?_, ?_⟩
        · rw [det_mul]
          exact hEdet.mul hVdet
        · calc
            (E * V)ᵀ * G * (E * V) = Vᵀ * (Eᵀ * G * E) * V := by
              simp only [transpose_mul]
              noncomm_ring
            _ = 1 := hV

/-- An everywhere positive-semidefinite symmetric polynomial matrix with unit determinant is
polynomially congruent to the identity. -/
theorem exists_transpose_mul_mul_eq_one_of_posSemidef_eval {n : Type*}
    [Fintype n] [DecidableEq n] {G : Matrix n n ℝ[X]} (hGsymm : Gᵀ = G)
    (hGdet : IsUnit G.det) (hGnonneg : ∀ x : ℝ, (G.map (evalRingHom x)).PosSemidef) :
    ∃ Q : Matrix n n ℝ[X], IsUnit Q.det ∧ Qᵀ * G * Q = 1 := by
  apply exists_transpose_mul_mul_eq_one_of_posDef_eval hGsymm hGdet
  intro x
  apply (hGnonneg x).posDef_iff_det_ne_zero.mpr
  change ((evalRingHom x).mapMatrix G).det ≠ 0
  simpa only [RingHom.map_det] using (hGdet.map (evalRingHom x)).ne_zero

/-- A symmetric polynomial matrix with unit determinant which is positive definite at one real
fiber is polynomially congruent to the identity. -/
theorem exists_transpose_mul_mul_eq_one_of_posDef_eval_at {n : Type*}
    [Fintype n] [DecidableEq n] {G : Matrix n n ℝ[X]} (hGsymm : Gᵀ = G)
    (hGdet : IsUnit G.det) {x₀ : ℝ} (hx₀ : (G.map (evalRingHom x₀)).PosDef) :
    ∃ Q : Matrix n n ℝ[X], IsUnit Q.det ∧ Qᵀ * G * Q = 1 := by
  let A : ℝ → Matrix n n ℝ := fun x => G.map (evalRingHom x)
  have hA : Continuous A := by
    apply continuous_matrix
    intro i j
    exact (G i j).continuous
  have hAsymm (x : ℝ) : (A x)ᵀ = A x := by
    simp only [A, ← transpose_map, hGsymm]
  have hdet (x : ℝ) : (A x).det ≠ 0 := by
    change ((evalRingHom x).mapMatrix G).det ≠ 0
    simpa only [RingHom.map_det] using (hGdet.map (evalRingHom x)).ne_zero
  apply exists_transpose_mul_mul_eq_one_of_posDef_eval hGsymm hGdet
  exact posDef_of_continuous_of_det_ne_zero A hA hAsymm hdet hx₀

/-- An everywhere positive-definite symmetric polynomial matrix with unit determinant is a
square polynomial Gram matrix of the same size, with a unimodular factor. -/
theorem exists_eq_transpose_mul_self_of_posDef_eval {n : Type*}
    [Fintype n] [DecidableEq n] {G : Matrix n n ℝ[X]} (hGsymm : Gᵀ = G)
    (hGdet : IsUnit G.det) (hGpos : ∀ x : ℝ, (G.map (evalRingHom x)).PosDef) :
    ∃ P : Matrix n n ℝ[X], IsUnit P.det ∧ G = Pᵀ * P := by
  obtain ⟨Q, hQdet, hQ⟩ :=
    exists_transpose_mul_mul_eq_one_of_posDef_eval hGsymm hGdet hGpos
  let P := Q⁻¹
  have hQP : Q * P = 1 := Q.mul_nonsing_inv hQdet
  refine ⟨P, Q.isUnit_nonsing_inv_det hQdet, ?_⟩
  calc
    G = (Q * P)ᵀ * G * (Q * P) := by rw [hQP]; simp only [transpose_one, one_mul, mul_one]
    _ = Pᵀ * (Qᵀ * G * Q) * P := by simp only [transpose_mul]; noncomm_ring
    _ = Pᵀ * P := by rw [hQ]; simp only [mul_one]

example :
    let G : Matrix (Fin 2) (Fin 2) ℝ[X] := !![1, X; X, 1 + X ^ 2]
    let E : Matrix (Fin 2) (Fin 2) ℝ[X] := !![1, -X; 0, 1]
    G.det = 1 ∧ Eᵀ * G * E = 1 := by
  dsimp
  constructor
  · norm_num [det_fin_two]
    ring
  · ext i j
    fin_cases i
    · fin_cases j
      · norm_num [Matrix.mul_apply, Fin.sum_univ_two]
      · norm_num [Matrix.mul_apply, Fin.sum_univ_two]
    · fin_cases j
      · norm_num [Matrix.mul_apply, Fin.sum_univ_two]
      · norm_num [Matrix.mul_apply, Fin.sum_univ_two]
        ring_nf
        simp

end Matrix
