module

public import RealRooted.Polarization

/-!
# The Grace–Walsh–Szegő coincidence theorem

Let `P` be a symmetric multiaffine polynomial in `z₁, …, zₙ` and let `C` be a circular region.
The coincidence theorem of Grace, Walsh and Szegő says that every value `P(ζ₁, …, ζₙ)` with all
`ζᵢ ∈ C` is also a diagonal value `P(ζ, …, ζ)` with `ζ ∈ C`, provided `C` is convex or the
diagonal `P(z, …, z)` has degree `n`.  We prove it for open and closed half-planes, open and
closed disks, and open and closed exteriors of disks.

The open upper half-plane case follows from the stability form
`mvUpperHalfPlaneStable_iff_eval_diagonalProjection_ne_zero`: the polynomial `P - P(ζ)` is
symmetric, multiaffine and vanishes at a point of the product of upper half-planes, so its
diagonal vanishes somewhere in the upper half-plane.  The multiaffine Möbius substitution
`multiaffineMobius` transports this to the other open regions; for exteriors the degree condition
excludes the pole of the Möbius map.  The closed regions follow by shrinking open regions onto
them, since the diagonal equation has only finitely many solutions.

## Main results

* `RealRooted.exists_eval_const_eq_of_im_pos`: open upper half-plane.
* `RealRooted.exists_eval_const_eq_of_im_div_pos`, `exists_eval_const_eq_of_im_div_nonneg`:
  open and closed half-planes `{z | 0 < ((z - b) / a).im}` and `{z | 0 ≤ ((z - b) / a).im}`.
* `RealRooted.exists_eval_const_eq_of_mem_ball`, `exists_eval_const_eq_of_mem_closedBall`:
  open and closed disks.
* `RealRooted.exists_eval_const_eq_of_lt_dist`, `exists_eval_const_eq_of_le_dist`: open and
  closed exteriors of disks, when the diagonal has degree `n`.

## References

J. L. Walsh, “On the location of the roots of certain types of polynomials,” *Trans. Amer. Math.
Soc.* 24 (1922), 163–180; G. Szegő, “Bemerkungen zu einem Satz von J. H. Grace über die Wurzeln
algebraischer Gleichungen,” *Math. Z.* 13 (1922), 28–55; Q. I. Rahman and G. Schmeisser,
*Analytic Theory of Polynomials*, Oxford University Press, 2002, Theorem 3.4.1b.
-/

@[expose] public section

namespace RealRooted

open MvPolynomial

section Mobius

variable {σ K : Type*} [Fintype σ]

/-- The factor that replaces the variable `X i` in the multiaffine Möbius substitution:
`a X i + b` if the monomial contains `X i`, and `c X i + d` otherwise. -/
noncomputable def mobiusFactor [CommRing K] (a b c d : K) (m : σ →₀ ℕ) :
    MvPolynomial σ K :=
  ∏ i, if m i = 0 then C c * X i + C d else C a * X i + C b

/-- **Multiaffine Möbius substitution.** For a multiaffine `P`, this is
`∏ i, (c zᵢ + d) · P((a z + b) / (c z + d))` with the denominators cleared: the monomial
`∏ i ∈ S, zᵢ` becomes `∏ i ∈ S, (a zᵢ + b) * ∏ i ∉ S, (c zᵢ + d)`. -/
noncomputable def multiaffineMobius [CommRing K] (a b c d : K) (P : MvPolynomial σ K) :
    MvPolynomial σ K :=
  ∑ m ∈ P.support, C (P.coeff m) * mobiusFactor a b c d m

private theorem multiaffineMobius_eq_sum [CommRing K] (a b c d : K) {P : MvPolynomial σ K}
    {s : Finset (σ →₀ ℕ)} (hs : P.support ⊆ s) :
    multiaffineMobius a b c d P = ∑ m ∈ s, C (P.coeff m) * mobiusFactor a b c d m :=
  Finset.sum_subset hs fun m _ hm => by simp [notMem_support_iff.1 hm]

/-- The multiaffine Möbius substitution is additive in the polynomial; here, for differences. -/
theorem multiaffineMobius_sub [CommRing K] (a b c d : K) (P Q : MvPolynomial σ K) :
    multiaffineMobius a b c d (P - Q) =
      multiaffineMobius a b c d P - multiaffineMobius a b c d Q := by
  classical
  rw [multiaffineMobius_eq_sum a b c d (support_sub σ P Q),
    multiaffineMobius_eq_sum a b c d Finset.subset_union_left,
    multiaffineMobius_eq_sum a b c d Finset.subset_union_right, ← Finset.sum_sub_distrib]
  simp [sub_mul]

/-- The substitution sends a constant `r` to `r ∏ i, (c Xᵢ + d)`. -/
theorem multiaffineMobius_C [CommRing K] (a b c d r : K) :
    multiaffineMobius a b c d (C r : MvPolynomial σ K) = C r * ∏ i, (C c * X i + C d) := by
  classical
  rw [multiaffineMobius_eq_sum a b c d (s := {0}) fun m hm => by
    rw [Finset.mem_singleton]; by_contra h; simp [coeff_C, Ne.symm h] at hm]
  simp [mobiusFactor]

omit [Fintype σ] in
private theorem degreeOf_C_mul_X_add_C_le [DecidableEq σ] [CommRing K] (x y : K) (i j : σ) :
    (C x * X j + C y : MvPolynomial σ K).degreeOf i ≤ if j = i then 1 else 0 := by
  classical
  refine (degreeOf_add_le _ _ _).trans (max_le ((degreeOf_C_mul_le _ _ _).trans ?_) ?_)
  · rcases subsingleton_or_nontrivial K with hK | hK
    · simp [Subsingleton.elim (X j : MvPolynomial σ K) 0]
    · rw [degreeOf_X]
      by_cases h : j = i
      · simp [h]
      · simp [h, Ne.symm h]
  · simp [degreeOf_C]

/-- The multiaffine Möbius substitution is multiaffine. -/
theorem isMultiaffine_multiaffineMobius [CommRing K] (a b c d : K) (P : MvPolynomial σ K) :
    (multiaffineMobius a b c d P).IsMultiaffine := by
  classical
  intro i
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun m _ => ?_)
  refine (degreeOf_C_mul_le _ _ _).trans ((degreeOf_prod_le _ _ _).trans ?_)
  calc ∑ j, degreeOf i (if m j = 0 then C c * X j + C d else C a * X j + C b :
          MvPolynomial σ K)
      ≤ ∑ j : σ, if j = i then 1 else 0 := Finset.sum_le_sum fun j _ => by
        by_cases h : m j = 0
        · simp only [h, ↓reduceIte]; exact degreeOf_C_mul_X_add_C_le _ _ _ _
        · simp only [h, ↓reduceIte]; exact degreeOf_C_mul_X_add_C_le _ _ _ _
    _ = 1 := by simp

private theorem rename_mobiusFactor [CommRing K] (a b c d : K) (e : Equiv.Perm σ)
    (m : σ →₀ ℕ) :
    rename e (mobiusFactor a b c d m : MvPolynomial σ K) =
      mobiusFactor a b c d (Finsupp.mapDomain e m) := by
  rw [mobiusFactor, mobiusFactor, map_prod]
  refine Fintype.prod_equiv e _ _ fun i => ?_
  simp only [Finsupp.mapDomain_apply_of_injective e.injective]
  split_ifs <;> simp

/-- The multiaffine Möbius substitution of a symmetric polynomial is symmetric. -/
theorem isSymmetric_multiaffineMobius [CommRing K] (a b c d : K) {P : MvPolynomial σ K}
    (hP : P.IsSymmetric) : (multiaffineMobius a b c d P).IsSymmetric := by
  classical
  intro e
  conv_rhs => rw [← hP e]
  rw [multiaffineMobius, multiaffineMobius, map_sum, support_rename_of_injective e.injective,
    Finset.sum_image fun _ _ _ _ h => Finsupp.mapDomain_injective e.injective h]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, rename_C, rename_mobiusFactor, coeff_rename_mapDomain _ e.injective]

private theorem eval_multiaffineMobius_eq [CommRing K] (a b c d : K) (P : MvPolynomial σ K)
    (w : σ → K) :
    eval w (multiaffineMobius a b c d P) =
      ∑ m ∈ P.support, P.coeff m * ∏ i, if m i = 0 then c * w i + d else a * w i + b := by
  rw [multiaffineMobius, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, eval_C, mobiusFactor, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- Away from the pole, the substitution evaluates to `∏ (c wᵢ + d) · P((a w + b) / (c w + d))`. -/
theorem eval_multiaffineMobius [Field K] (a b c d : K) {P : MvPolynomial σ K}
    (hP : P.IsMultiaffine) (w : σ → K) (hw : ∀ i, c * w i + d ≠ 0) :
    eval w (multiaffineMobius a b c d P) =
      (∏ i, (c * w i + d)) * eval (fun i => (a * w i + b) / (c * w i + d)) P := by
  rw [eval_multiaffineMobius_eq, eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (degreeOf_le_iff.mp (hP i) m hm) with h | h
  · simp [h]
  · simp [h, mul_div_cancel₀ _ (hw i)]

/-- At the pole `c wᵢ + d = 0` in every coordinate only the top monomial `z₁ ⋯ zₙ` survives. -/
theorem eval_multiaffineMobius_of_forall_eq_zero [CommRing K] (a b c d : K)
    {P : MvPolynomial σ K} (hP : P.IsMultiaffine) (w : σ → K) (hw : ∀ i, c * w i + d = 0) :
    eval w (multiaffineMobius a b c d P) =
      P.coeff (∑ i, Finsupp.single i 1) * ∏ i, (a * w i + b) := by
  classical
  have hm0 : ∀ i, (∑ j, Finsupp.single j 1 : σ →₀ ℕ) i = 1 := fun i => by
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [eval_multiaffineMobius_eq, Finset.sum_eq_single (∑ j, Finsupp.single j 1)]
  · congr 1
    exact Finset.prod_congr rfl fun i _ => by simp [hm0 i]
  · intro m hm hne
    obtain ⟨i, hi⟩ : ∃ i, m i = 0 := by
      by_contra! h
      exact hne (Finsupp.ext fun i => by
        have := degreeOf_le_iff.mp (hP i) m hm
        have := h i
        rw [hm0 i]
        lia)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hw i]), mul_zero]
  · intro h
    rw [notMem_support_iff.mp h, zero_mul]

end Mobius

open Polynomial Complex

private theorem normSq_sub_I_lt {u : ℂ} (hu : 0 < u.im) : normSq (u - I) < normSq (u + I) := by
  simp only [normSq_apply, sub_re, I_re, sub_im, I_im, add_re, add_im]
  nlinarith

private theorem add_I_ne_zero {u : ℂ} (hu : 0 < u.im) : u + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The Cayley map `u ↦ c + r (u - I) / (u + I)` sends the upper half-plane into the disk. -/
private theorem cayley_mem_ball {c : ℂ} {r : ℝ} (hr : 0 < r) {u : ℂ} (hu : 0 < u.im) :
    c + r * ((u - I) / (u + I)) ∈ Metric.ball c r := by
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hr.le]
  have h1 : ‖u - I‖ < ‖u + I‖ := by
    rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    exact normSq_sub_I_lt hu
  have h2 : 0 < ‖u + I‖ := norm_pos_iff.2 (add_I_ne_zero hu)
  calc r * (‖u - I‖ / ‖u + I‖) < r * 1 := by
        gcongr; exact (div_lt_one h2).2 h1
    _ = r := mul_one r

/-- Inverse Cayley point of a point of the disk lies in the upper half-plane. -/
private theorem im_cayleyInv_pos {c ζ : ℂ} {r : ℝ} (hζ : ζ ∈ Metric.ball c r) :
    0 < (I * ((r + (ζ - c)) / (r - (ζ - c)))).im := by
  rw [Metric.mem_ball, dist_eq_norm] at hζ
  set t := ζ - c
  have ht : normSq t < r ^ 2 := by
    rw [normSq_eq_norm_sq]; exact pow_lt_pow_left₀ hζ (norm_nonneg _) two_ne_zero
  have hne : (r : ℂ) - t ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h, Complex.norm_real] at hζ
    exact (lt_irrefl _ (lt_of_le_of_lt (Real.le_norm_self r) hζ))
  rw [mul_im, I_re, I_im, zero_mul, one_mul, zero_add, div_re]
  have hpos : 0 < normSq ((r : ℂ) - t) := normSq_pos.2 hne
  rw [← add_div]
  apply div_pos _ hpos
  simp only [add_re, ofReal_re, sub_re, add_im, ofReal_im, sub_im, zero_add, zero_sub]
  rw [normSq_apply] at ht
  nlinarith


/-- A symmetric multiaffine polynomial vanishing at a point of the product of open upper
half-planes vanishes on the diagonal at a point of the open upper half-plane. -/
theorem exists_eval_const_eq_zero_of_im_pos {n : ℕ} {Q : MvPolynomial (Fin n) ℂ}
    (hsym : Q.IsSymmetric) (hma : Q.IsMultiaffine) {ζ : Fin n → ℂ}
    (hζ : ∀ i, 0 < (ζ i).im) (h0 : MvPolynomial.eval ζ Q = 0) :
    ∃ w : ℂ, 0 < w.im ∧ MvPolynomial.eval (fun _ => w) Q = 0 := by
  have hQ : ¬ MvUpperHalfPlaneStable Q := fun h => h ζ hζ h0
  rw [mvUpperHalfPlaneStable_iff_eval_diagonalProjection_ne_zero hsym hma] at hQ
  push Not at hQ
  obtain ⟨w, hw, h⟩ := hQ
  exact ⟨w, hw, by rwa [eval_diagonalProjection] at h⟩

/-- Möbius step: pull a point of the image region back to the upper half-plane. -/
private theorem exists_eval_multiaffineMobius_eq_zero {n : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hsym : P.IsSymmetric) (hma : P.IsMultiaffine) (a b c d : ℂ) {w : Fin n → ℂ}
    (hw : ∀ i, 0 < (w i).im) (hd : ∀ i, c * w i + d ≠ 0) :
    ∃ u : ℂ, 0 < u.im ∧ MvPolynomial.eval (fun _ => u) (multiaffineMobius a b c d
      (P - MvPolynomial.C (MvPolynomial.eval (fun i => (a * w i + b) / (c * w i + d)) P))) =
        0 := by
  set v := MvPolynomial.eval (fun i => (a * w i + b) / (c * w i + d)) P
  have hma' : (P - MvPolynomial.C v).IsMultiaffine := hma.sub (MvPolynomial.IsMultiaffine.C _)
  refine exists_eval_const_eq_zero_of_im_pos
    (isSymmetric_multiaffineMobius a b c d (hsym.sub (MvPolynomial.IsSymmetric.C v)))
    (isMultiaffine_multiaffineMobius a b c d _) hw ?_
  rw [eval_multiaffineMobius a b c d hma' w hd]
  simp [v]

/-- **Grace–Walsh–Szegő coincidence theorem**, open upper half-plane. -/
theorem exists_eval_const_eq_of_im_pos {n : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hsym : P.IsSymmetric) (hma : P.IsMultiaffine) {ζ : Fin n → ℂ}
    (hζ : ∀ i, 0 < (ζ i).im) :
    ∃ w : ℂ, 0 < w.im ∧ MvPolynomial.eval (fun _ => w) P = MvPolynomial.eval ζ P := by
  obtain ⟨w, hw, h⟩ := exists_eval_const_eq_zero_of_im_pos
    (hsym.sub (MvPolynomial.IsSymmetric.C (MvPolynomial.eval ζ P)))
    (hma.sub (MvPolynomial.IsMultiaffine.C _)) hζ (by simp)
  exact ⟨w, hw, by simpa [sub_eq_zero] using h⟩

/-- **Grace–Walsh–Szegő coincidence theorem**, open half-planes
`{z | 0 < ((z - b) / a).im}`. -/
theorem exists_eval_const_eq_of_im_div_pos {n : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hsym : P.IsSymmetric) (hma : P.IsMultiaffine) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    {ζ : Fin n → ℂ} (hζ : ∀ i, 0 < ((ζ i - b) / a).im) :
    ∃ w : ℂ, 0 < ((w - b) / a).im ∧
      MvPolynomial.eval (fun _ => w) P = MvPolynomial.eval ζ P := by
  have hζ' : (fun i => (a * ((ζ i - b) / a) + b) / (0 * ((ζ i - b) / a) + 1)) = ζ := by
    ext i; simp [mul_div_cancel₀ _ ha]
  obtain ⟨u, hu, h⟩ := exists_eval_multiaffineMobius_eq_zero hsym hma a b 0 1 hζ (by simp)
  rw [hζ'] at h
  rw [eval_multiaffineMobius a b 0 1 (hma.sub (MvPolynomial.IsMultiaffine.C _)) _ (by simp)]
    at h
  refine ⟨a * u + b, by simpa [mul_div_cancel_left₀ _ ha] using hu, ?_⟩
  simpa [sub_eq_zero] using h

/-- **Grace–Walsh–Szegő coincidence theorem**, open disks. -/
theorem exists_eval_const_eq_of_mem_ball {n : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hsym : P.IsSymmetric) (hma : P.IsMultiaffine) {c : ℂ} {r : ℝ} (hr : 0 < r)
    {ζ : Fin n → ℂ} (hζ : ∀ i, ζ i ∈ Metric.ball c r) :
    ∃ w ∈ Metric.ball c r, MvPolynomial.eval (fun _ => w) P = MvPolynomial.eval ζ P := by
  set w : Fin n → ℂ := fun i => I * ((r + (ζ i - c)) / (r - (ζ i - c)))
  have hw : ∀ i, 0 < (w i).im := fun i => im_cayleyInv_pos (hζ i)
  have hd : ∀ i, 1 * w i + I ≠ 0 := fun i => by simpa using add_I_ne_zero (hw i)
  have hζ' : (fun i => ((c + r) * w i + I * (c - r)) / (1 * w i + I)) = ζ := by
    ext i
    have hne : (r : ℂ) - (ζ i - c) ≠ 0 := by
      intro h
      have := hζ i
      rw [Metric.mem_ball, dist_eq_norm, ← sub_eq_zero.1 h, Complex.norm_real] at this
      exact lt_irrefl _ (lt_of_le_of_lt (Real.le_norm_self r) this)
    rw [div_eq_iff (hd i)]
    simp only [w]
    field_simp
    ring
  obtain ⟨u, hu, h⟩ :=
    exists_eval_multiaffineMobius_eq_zero hsym hma (c + r) (I * (c - r)) 1 I hw hd
  rw [hζ'] at h
  have hu' : 1 * u + I ≠ 0 := by simpa using add_I_ne_zero hu
  rw [eval_multiaffineMobius _ _ _ _ (hma.sub (MvPolynomial.IsMultiaffine.C _)) _
    (fun _ => hu')] at h
  have hcay : ((c + r) * u + I * (c - r)) / (1 * u + I) = c + r * ((u - I) / (u + I)) := by
    rw [one_mul] at hu' ⊢
    field_simp
    ring
  refine ⟨c + r * ((u - I) / (u + I)), cayley_mem_ball hr hu, ?_⟩
  rw [← hcay]
  simpa [sub_eq_zero, add_I_ne_zero hu] using h

/-- If every member of a decreasing sequence of sets contains a root of a nonzero polynomial,
then some root lies in all of them. -/
private theorem exists_isRoot_forall_mem {q : ℂ[X]} (hq : q ≠ 0) {S : ℕ → Set ℂ}
    (hS : Antitone S) (h : ∀ k, ∃ z ∈ S k, q.IsRoot z) :
    ∃ z, q.IsRoot z ∧ ∀ k, z ∈ S k := by
  by_contra! hcon
  choose! K hK using hcon
  obtain ⟨z, hz, hr⟩ := h (q.roots.toFinset.sup K)
  have hmem : z ∈ q.roots.toFinset := by simpa [hq] using hr
  exact hK z hr (hS (Finset.le_sup hmem) hz)


/-- **Grace–Walsh–Szegő coincidence theorem**, closed disks. -/
theorem exists_eval_const_eq_of_mem_closedBall {n : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hsym : P.IsSymmetric) (hma : P.IsMultiaffine) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    {ζ : Fin n → ℂ} (hζ : ∀ i, ζ i ∈ Metric.closedBall c r) :
    ∃ w ∈ Metric.closedBall c r, MvPolynomial.eval (fun _ => w) P = MvPolynomial.eval ζ P := by
  set v := MvPolynomial.eval ζ P
  set q : ℂ[X] := diagonalProjection n P - Polynomial.C v
  have hroot : ∀ z, q.IsRoot z ↔ MvPolynomial.eval (fun _ => z) P = v := by
    intro z; simp [q, eval_diagonalProjection, sub_eq_zero]
  by_cases hq : q = 0
  · exact ⟨c, Metric.mem_closedBall_self hr, (hroot c).1 (by simp [hq])⟩
  obtain ⟨z, hz, hS⟩ := exists_isRoot_forall_mem hq
    (S := fun k : ℕ => Metric.ball c (r + 1 / (k + 1)))
    (fun k l hkl => Metric.ball_subset_ball (by gcongr))
    (fun k => by
      obtain ⟨w, hw, h⟩ := exists_eval_const_eq_of_mem_ball hsym hma
        (by positivity : 0 < r + 1 / ((k : ℝ) + 1))
        fun i => Metric.closedBall_subset_ball (lt_add_of_pos_right r (by positivity)) (hζ i)
      exact ⟨w, hw, (hroot w).2 h⟩)
  refine ⟨z, ?_, (hroot z).1 hz⟩
  rw [Metric.mem_closedBall]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have := Metric.mem_ball.1 (hS k)
  linarith

/-- **Grace–Walsh–Szegő coincidence theorem**, closed half-planes
`{z | 0 ≤ ((z - b) / a).im}`. -/
theorem exists_eval_const_eq_of_im_div_nonneg {n : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hsym : P.IsSymmetric) (hma : P.IsMultiaffine) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    {ζ : Fin n → ℂ} (hζ : ∀ i, 0 ≤ ((ζ i - b) / a).im) :
    ∃ w : ℂ, 0 ≤ ((w - b) / a).im ∧
      MvPolynomial.eval (fun _ => w) P = MvPolynomial.eval ζ P := by
  set v := MvPolynomial.eval ζ P
  set q : ℂ[X] := diagonalProjection n P - Polynomial.C v
  have hroot : ∀ z, q.IsRoot z ↔ MvPolynomial.eval (fun _ => z) P = v := by
    intro z; simp [q, eval_diagonalProjection, sub_eq_zero]
  by_cases hq : q = 0
  · exact ⟨b, by simp, (hroot b).1 (by simp [hq])⟩
  have hshift : ∀ (z : ℂ) (t : ℝ), ((z - (b - a * (I * t))) / a).im = ((z - b) / a).im + t := by
    intro z t
    have : (z - (b - a * (I * t))) / a = (z - b) / a + I * t := by field_simp; ring
    simp [this]
  obtain ⟨z, hz, hS⟩ := exists_isRoot_forall_mem hq
    (S := fun k : ℕ => {z | -(1 / ((k : ℝ) + 1)) < ((z - b) / a).im})
    (fun k l hkl z hz => by
      simp only [Set.mem_ofPred_eq] at hz ⊢
      have : 1 / ((l : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by gcongr
      linarith)
    (fun k => by
      obtain ⟨w, hw, h⟩ := exists_eval_const_eq_of_im_div_pos hsym hma ha
        (b - a * (I * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ))) (ζ := ζ)
        fun i => by rw [hshift]; have := hζ i; positivity
      refine ⟨w, ?_, (hroot w).2 h⟩
      rw [hshift] at hw
      simp only [Set.mem_ofPred_eq]
      linarith)
  refine ⟨z, ?_, (hroot z).1 hz⟩
  by_contra! hneg
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (neg_pos.2 hneg)
  have := hS k
  simp only [Set.mem_ofPred_eq] at this
  linarith

/-- For a symmetric multiaffine `P`, the top coefficient of the diagonal is the coefficient of
`z₁ ⋯ zₙ`. -/
theorem coeff_diagonalProjection_self {n : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hsym : P.IsSymmetric) (hma : P.IsMultiaffine) :
    (diagonalProjection n P).coeff n = P.coeff (∑ i, Finsupp.single i 1) := by
  conv_lhs => rw [hsym.eq_sum_C_mul_esymm hma]
  simp only [map_sum, ← MvPolynomial.smul_eq_C_mul, map_smul, diagonalProjection_esymm,
    Polynomial.finsetSum_coeff, Polynomial.coeff_smul, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single n (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  simp

/-- Inverse Cayley point of a point outside the closed disk lies in the upper half-plane. -/
private theorem im_cayleyInv_pos_of_lt_dist {c ζ : ℂ} {r : ℝ} (hr : 0 < r)
    (hζ : r < dist ζ c) : 0 < (I * ((ζ - c + r) / (ζ - c - r))).im := by
  rw [dist_eq_norm] at hζ
  set t := ζ - c
  have ht : r ^ 2 < normSq t := by
    rw [normSq_eq_norm_sq]; exact pow_lt_pow_left₀ hζ hr.le two_ne_zero
  have hne : t - (r : ℂ) ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, Complex.norm_real, Real.norm_of_nonneg hr.le] at hζ
    exact lt_irrefl _ hζ
  rw [mul_im, I_re, I_im, zero_mul, one_mul, zero_add, div_re, ← add_div]
  apply div_pos _ (normSq_pos.2 hne)
  simp only [add_re, ofReal_re, sub_re, add_im, ofReal_im, sub_im, add_zero, sub_zero]
  rw [normSq_apply] at ht
  nlinarith

/-- **Grace–Walsh–Szegő coincidence theorem**, open exterior of a disk: if the diagonal of
`P` has full degree `n`, then every value of `P` on the exterior is a diagonal value there. -/
theorem exists_eval_const_eq_of_lt_dist {n : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hsym : P.IsSymmetric) (hma : P.IsMultiaffine)
    (hdeg : (diagonalProjection n P).natDegree = n) {c : ℂ} {r : ℝ} (hr : 0 < r)
    {ζ : Fin n → ℂ} (hζ : ∀ i, r < dist (ζ i) c) :
    ∃ w, r < dist w c ∧ MvPolynomial.eval (fun _ => w) P = MvPolynomial.eval ζ P := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨c + ((2 * r : ℝ) : ℂ), ?_,
      congrArg (fun z => MvPolynomial.eval z P) (Subsingleton.elim _ _)⟩
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  set w : Fin n → ℂ := fun i => I * ((ζ i - c + r) / (ζ i - c - r))
  have hne : ∀ i, ζ i - c - (r : ℂ) ≠ 0 := fun i h => by
    have := hζ i
    rw [dist_eq_norm, sub_eq_zero.1 h, Complex.norm_real, Real.norm_of_nonneg hr.le] at this
    exact lt_irrefl _ this
  have hw : ∀ i, 0 < (w i).im := fun i => im_cayleyInv_pos_of_lt_dist hr (hζ i)
  have hd : ∀ i, 1 * w i + -I ≠ 0 := fun i => by
    have hr0 : (2 * r : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast hr.ne')
    have : 1 * w i + -I = I * (2 * r) / (ζ i - c - r) := by
      simp only [w]
      field_simp [hne i]
      ring
    rw [this]
    exact div_ne_zero (mul_ne_zero I_ne_zero hr0) (hne i)
  have hζ' : (fun i => ((c + r) * w i + I * (r - c)) / (1 * w i + -I)) = ζ := by
    ext i
    rw [div_eq_iff (hd i)]
    simp only [w]
    field_simp [hne i]
    ring_nf
  obtain ⟨u, hu, h⟩ :=
    exists_eval_multiaffineMobius_eq_zero hsym hma (c + r) (I * (r - c)) 1 (-I) hw hd
  rw [hζ'] at h
  have hmaQ := hma.sub (MvPolynomial.IsMultiaffine.C (MvPolynomial.eval ζ P))
  by_cases huI : u = I
  · exfalso
    subst huI
    rw [eval_multiaffineMobius_of_forall_eq_zero _ _ _ _ hmaQ _ (fun _ => by ring)] at h
    have hone : (∑ i : Fin n, Finsupp.single i 1 : Fin n →₀ ℕ) ≠ 0 := fun h0 => by
      have := congrArg (fun f => f ⟨0, hn⟩) h0
      simp [Finsupp.finsetSum_apply, Finsupp.single_apply] at this
    have hlc : P.coeff (∑ i, Finsupp.single i 1) ≠ 0 := by
      have h0 : diagonalProjection n P ≠ 0 := fun h0 => by
        rw [h0, Polynomial.natDegree_zero] at hdeg
        lia
      have := Polynomial.leadingCoeff_ne_zero.2 h0
      rwa [Polynomial.leadingCoeff, hdeg, coeff_diagonalProjection_self hsym hma] at this
    have hfac : (c + r) * I + I * (r - c) ≠ 0 := by
      have : (c + r) * I + I * (r - c) = 2 * r * I := by ring
      rw [this]
      exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hr.ne')) I_ne_zero
    simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, Ne.symm hone, ↓reduceIte,
      sub_zero, Finset.prod_const] at h
    exact mul_ne_zero hlc (pow_ne_zero _ hfac) h
  have hu' : 1 * u + -I ≠ 0 := by simpa [sub_eq_add_neg] using sub_ne_zero.2 huI
  rw [eval_multiaffineMobius _ _ _ _ hmaQ _ (fun _ => hu')] at h
  have hcay : ((c + r) * u + I * (r - c)) / (1 * u + -I) = c + r * ((u + I) / (u - I)) := by
    have : u - I ≠ 0 := sub_ne_zero.2 huI
    rw [one_mul, ← sub_eq_add_neg]
    field_simp
    ring
  refine ⟨c + r * ((u + I) / (u - I)), ?_, ?_⟩
  · rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
    have h1 : ‖u - I‖ < ‖u + I‖ := by
      rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq,
        ← normSq_eq_norm_sq]
      exact normSq_sub_I_lt hu
    have h2 : 0 < ‖u - I‖ := norm_pos_iff.2 (sub_ne_zero.2 huI)
    calc r = r * 1 := (mul_one r).symm
      _ < r * (‖u + I‖ / ‖u - I‖) := by gcongr; exact (one_lt_div h2).2 h1
  · rw [← hcay]
    have hu2 : u + -I ≠ 0 := by simpa using hu'
    simpa [sub_eq_zero, hu2] using h

/-- **Grace–Walsh–Szegő coincidence theorem**, closed exterior of a disk. -/
theorem exists_eval_const_eq_of_le_dist {n : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hsym : P.IsSymmetric) (hma : P.IsMultiaffine)
    (hdeg : (diagonalProjection n P).natDegree = n) {c : ℂ} {r : ℝ} (hr : 0 < r)
    {ζ : Fin n → ℂ} (hζ : ∀ i, r ≤ dist (ζ i) c) :
    ∃ w, r ≤ dist w c ∧ MvPolynomial.eval (fun _ => w) P = MvPolynomial.eval ζ P := by
  set v := MvPolynomial.eval ζ P
  set q : ℂ[X] := diagonalProjection n P - Polynomial.C v
  have hroot : ∀ z, q.IsRoot z ↔ MvPolynomial.eval (fun _ => z) P = v := by
    intro z; simp [q, eval_diagonalProjection, sub_eq_zero]
  by_cases hq : q = 0
  · refine ⟨c + r, ?_, (hroot _).1 (by simp [hq])⟩
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hr.le]
  obtain ⟨z, hz, hS⟩ := exists_isRoot_forall_mem hq
    (S := fun k : ℕ => {z | r - r / ((k : ℝ) + 2) < dist z c})
    (fun k l hkl z hz => by
      simp only [Set.mem_ofPred_eq] at hz ⊢
      have : r / ((l : ℝ) + 2) ≤ r / ((k : ℝ) + 2) := by gcongr
      exact lt_of_le_of_lt (sub_le_sub_left this r) hz)
    (fun k => by
      have hk : r / ((k : ℝ) + 2) < r := div_lt_self hr (by linarith [k.cast_nonneg (α := ℝ)])
      obtain ⟨w, hw, h⟩ := exists_eval_const_eq_of_lt_dist hsym hma hdeg
        (sub_pos.2 hk) fun i =>
          lt_of_lt_of_le (sub_lt_self r (by positivity)) (hζ i)
      exact ⟨w, hw, (hroot w).2 h⟩)
  refine ⟨z, ?_, (hroot z).1 hz⟩
  by_contra! hlt
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos (sub_pos.2 hlt) hr)
  have := hS k
  simp only [Set.mem_ofPred_eq] at this
  have h2 : r / ((k : ℝ) + 2) < r - dist z c := by
    have h3 : r / ((k : ℝ) + 2) ≤ r * (1 / ((k : ℝ) + 1)) := by
      rw [mul_one_div]; gcongr; linarith
    calc r / ((k : ℝ) + 2) ≤ r * (1 / ((k : ℝ) + 1)) := h3
      _ < r * ((r - dist z c) / r) := by gcongr
      _ = r - dist z c := by field_simp
  generalize r / ((k : ℝ) + 2) = δ at this h2
  linarith

end RealRooted
