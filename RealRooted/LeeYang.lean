import Mathlib

/-!
# The Lee–Yang circle theorem

We prove the Lee–Yang circle theorem in its multiaffine (partition-function) form: for a finite
type `ι` and a real symmetric matrix `a` with `|a i j| ≤ 1`, the polynomial
`∑ S, (∏ i ∈ S, ∏ j ∈ Sᶜ, a i j) * ∏ i ∈ S, z i` does not vanish on the open unit polydisc,
and its diagonal specialisation has all of its zeros on the unit circle.

The proof follows the Asano contraction method.

## References

* T. D. Lee and C. N. Yang, *Statistical theory of equations of state and phase transitions.
  II. Lattice gas and Ising model*, Phys. Rev. 87 (1952), 410–419.
* T. Asano, *Lee–Yang theorem and the Griffiths inequality for the anisotropic Heisenberg
  ferromagnet*, Phys. Rev. Lett. 24 (1970), 1409–1411.
* D. Ruelle, *Characterization of Lee–Yang polynomials*, Ann. of Math. 171 (2010), 589–603.
-/

open Finset

namespace RealRooted.LeeYang

/-! ### Scalar lemmas -/

/-- If `p + q * u` has no zero in the open unit disc, then `‖q‖ ≤ ‖p‖`. -/
theorem norm_le_of_forall_add_mul_ne_zero {p q : ℂ}
    (h : ∀ u : ℂ, ‖u‖ < 1 → p + q * u ≠ 0) : ‖q‖ ≤ ‖p‖ := by
  by_contra hlt
  have hlt : ‖p‖ < ‖q‖ := not_le.mp hlt
  have hq : q ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hlt
    linarith [norm_nonneg p]
  refine h (-p / q) ?_ ?_
  · rw [norm_div, norm_neg, div_lt_one (norm_pos_iff.mpr hq)]
    exact hlt
  · field_simp
    ring

/-- The parallelogram law in `ℂ`, with squared norms. -/
theorem norm_add_sq_add_norm_sub_sq (x y : ℂ) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im]
  ring

/-- **Asano contraction**, scalar form (Asano 1970; see also Ruelle 2010).
If `α + β u + γ v + δ u v` has no zero for `‖u‖ < 1` and `‖v‖ < 1`, then `α + δ z` has no zero
for `‖z‖ < 1`. -/
theorem asano_contraction {α β γ δ : ℂ}
    (h : ∀ u v : ℂ, ‖u‖ < 1 → ‖v‖ < 1 → α + β * u + γ * v + δ * (u * v) ≠ 0)
    {z : ℂ} (hz : ‖z‖ < 1) : α + δ * z ≠ 0 := by
  have hα : α ≠ 0 := by simpa using h 0 0 (by simp) (by simp)
  set t : ℝ := (1 + ‖z‖) / 2 with ht
  have hz0 := norm_nonneg z
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := by linarith
  have hzt : ‖z‖ < t := by linarith
  have htn : ‖(t : ℂ)‖ = t := by simp [abs_of_nonneg ht0]
  have htn' : ‖-(t : ℂ)‖ = t := by rw [norm_neg, htn]
  have H1 : ∀ v : ℂ, ‖v‖ < 1 → ‖β + δ * v‖ ≤ ‖α + γ * v‖ := fun v hv =>
    norm_le_of_forall_add_mul_ne_zero fun u hu h0 => h u v hu hv (by linear_combination h0)
  have H2 : ∀ u : ℂ, ‖u‖ < 1 → ‖γ + δ * u‖ ≤ ‖α + β * u‖ := fun u hu =>
    norm_le_of_forall_add_mul_ne_zero fun v hv h0 => h u v hu hv (by linear_combination h0)
  have e1 := H1 t (by rwa [htn])
  have e2 := H1 (-t) (by rwa [htn'])
  have e3 := H2 t (by rwa [htn])
  have e4 := H2 (-t) (by rwa [htn'])
  rw [show β + δ * -(t : ℂ) = β - δ * t by ring,
    show α + γ * -(t : ℂ) = α - γ * t by ring] at e2
  rw [show γ + δ * -(t : ℂ) = γ - δ * t by ring,
    show α + β * -(t : ℂ) = α - β * t by ring] at e4
  have p1 := norm_add_sq_add_norm_sub_sq β (δ * t)
  have p2 := norm_add_sq_add_norm_sub_sq α (γ * t)
  have p3 := norm_add_sq_add_norm_sub_sq γ (δ * t)
  have p4 := norm_add_sq_add_norm_sub_sq α (β * t)
  simp only [norm_mul, htn] at p1 p2 p3 p4
  have s1 := pow_le_pow_left₀ (norm_nonneg _) e1 2
  have s2 := pow_le_pow_left₀ (norm_nonneg _) e2 2
  have s3 := pow_le_pow_left₀ (norm_nonneg _) e3 2
  have s4 := pow_le_pow_left₀ (norm_nonneg _) e4 2
  have hb : 0 ≤ (1 - t ^ 2) * ‖β‖ ^ 2 := by
    have : t ^ 2 ≤ 1 := by nlinarith
    have : 0 ≤ 1 - t ^ 2 := by linarith
    positivity
  have hc : 0 ≤ (1 - t ^ 2) * ‖γ‖ ^ 2 := by
    have : t ^ 2 ≤ 1 := by nlinarith
    have : 0 ≤ 1 - t ^ 2 := by linarith
    positivity
  have key : t ^ 2 * ‖δ‖ ^ 2 ≤ ‖α‖ ^ 2 := by nlinarith
  intro h0
  have hαz : ‖α‖ = ‖δ‖ * ‖z‖ := by
    rw [← norm_mul, show α = -(δ * z) by linear_combination h0, norm_neg]
  have hD : 0 < ‖δ‖ := by
    rcases (norm_nonneg δ).lt_or_eq with hD | hD
    · exact hD
    · rw [← hD, zero_mul] at hαz
      exact absurd (norm_eq_zero.mp hαz) hα
  rw [hαz, mul_pow, mul_comm (t ^ 2)] at key
  have := le_of_mul_le_mul_left key (pow_pos hD 2)
  nlinarith

/-- For real `|c| ≤ 1` and `‖v‖ ≤ 1` we have `‖c + v‖ ≤ ‖1 + c v‖`. -/
theorem norm_ofReal_add_le_norm_one_add_mul {c : ℝ} (hc : |c| ≤ 1) {v : ℂ} (hv : ‖v‖ ≤ 1) :
    ‖(c : ℂ) + v‖ ≤ ‖1 + c * v‖ := by
  have h1 : ‖(1 : ℂ) + c * v‖ ^ 2 - ‖(c : ℂ) + v‖ ^ 2 = (1 - c ^ 2) * (1 - ‖v‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
      Complex.one_im]
    ring
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [abs_nonneg c, sq_abs c]
  have hv2 : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
  have hsq : ‖(c : ℂ) + v‖ ^ 2 ≤ ‖1 + c * v‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hc2) (sub_nonneg.2 hv2)]
  nlinarith [norm_nonneg ((c : ℂ) + v), norm_nonneg ((1 : ℂ) + c * v)]

/-- **Two-site Lee–Yang lemma.** For real `|c| ≤ 1`, the polynomial `1 + c z₁ + c z₂ + z₁ z₂`
has no zero with `‖z₁‖ < 1` and `‖z₂‖ < 1` (Lee–Yang 1952). -/
theorem two_site_ne_zero {c : ℝ} (hc : |c| ≤ 1) {v₁ v₂ : ℂ} (h₁ : ‖v₁‖ < 1)
    (h₂ : ‖v₂‖ < 1) : 1 + c * v₁ + c * v₂ + v₁ * v₂ ≠ 0 := by
  intro h
  have e : 1 + (c : ℂ) * v₂ = -(v₁ * (c + v₂)) := by linear_combination h
  have hle := norm_ofReal_add_le_norm_one_add_mul hc h₂.le
  have hn : ‖1 + (c : ℂ) * v₂‖ = ‖v₁‖ * ‖(c : ℂ) + v₂‖ := by rw [e, norm_neg, norm_mul]
  have h0 : ‖(c : ℂ) + v₂‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    nlinarith [norm_nonneg ((c : ℂ) + v₂), norm_nonneg v₁]
  have hv : v₂ = -c := by linear_combination norm_eq_zero.mp h0
  have h1 : (1 : ℂ) + c * v₂ = 0 := norm_eq_zero.mp (by rw [hn, h0, mul_zero])
  rw [hv] at h1 h₂
  have hc1 : ((1 - c ^ 2 : ℝ) : ℂ) = 0 := by
    push_cast
    linear_combination h1
  have hc1' : (1 - c ^ 2 : ℝ) = 0 := by exact_mod_cast hc1
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at h₂
  nlinarith [abs_nonneg c, sq_abs c]

/-- **Edge contraction.** Multiplying a two-variable nonvanishing polynomial by a Lee–Yang
two-site factor and contracting twice: if `A + B u₁ + C u₂ + D u₁ u₂` has no zero on the open
bidisc and `c` is real with `|c| ≤ 1`, then neither has `A + c B z₁ + c C z₂ + D z₁ z₂`. -/
theorem edge_contraction {A B C D : ℂ} {c : ℝ} (hc : |c| ≤ 1)
    (h : ∀ u₁ u₂ : ℂ, ‖u₁‖ < 1 → ‖u₂‖ < 1 → A + B * u₁ + C * u₂ + D * (u₁ * u₂) ≠ 0)
    {z₁ z₂ : ℂ} (hz₁ : ‖z₁‖ < 1) (hz₂ : ‖z₂‖ < 1) :
    A + c * B * z₁ + c * C * z₂ + D * (z₁ * z₂) ≠ 0 := by
  have step₁ : ∀ u₂ v₂ : ℂ, ‖u₂‖ < 1 → ‖v₂‖ < 1 →
      (A + C * u₂) * (1 + c * v₂) + (B + D * u₂) * (c + v₂) * z₁ ≠ 0 := by
    intro u₂ v₂ hu₂ hv₂
    refine asano_contraction (β := (B + D * u₂) * (1 + c * v₂))
      (γ := (A + C * u₂) * (c + v₂)) ?_ hz₁
    intro u₁ v₁ hu₁ hv₁ h0
    refine mul_ne_zero (h u₁ u₂ hu₁ hu₂) (two_site_ne_zero hc hv₁ hv₂) ?_
    linear_combination h0
  have step₂ : ∀ u₂ v₂ : ℂ, ‖u₂‖ < 1 → ‖v₂‖ < 1 →
      (A + c * B * z₁) + (C + c * D * z₁) * u₂ + (c * A + B * z₁) * v₂ +
        (c * C + D * z₁) * (u₂ * v₂) ≠ 0 := by
    intro u₂ v₂ hu₂ hv₂ h0
    exact step₁ u₂ v₂ hu₂ hv₂ (by linear_combination h0)
  intro h0
  exact asano_contraction step₂ hz₂ (by linear_combination h0)

/-! ### Multiaffine polynomials -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The multiaffine polynomial `∑ S, w S * ∏ i ∈ S, z i` with coefficients `w` has no zero on the
open unit polydisc. -/
def PolydiscNonvanishing (w : Finset ι → ℂ) : Prop :=
  ∀ z : ι → ℂ, (∀ i, ‖z i‖ < 1) → ∑ S : Finset ι, w S * ∏ i ∈ S, z i ≠ 0

omit [DecidableEq ι] in
/-- The constant coefficient function `1`, i.e. the polynomial `∏ i, (1 + z i)`, is
nonvanishing on the open unit polydisc. -/
theorem polydiscNonvanishing_one : PolydiscNonvanishing (fun _ : Finset ι => (1 : ℂ)) := by
  classical
  intro z hz
  have : ∑ S : Finset ι, (1 : ℂ) * ∏ i ∈ S, z i = ∏ i, (z i + 1) := by
    rw [Finset.prod_add, ← Finset.powerset_univ]
    simp
  rw [this, Finset.prod_ne_zero_iff]
  intro i _ h0
  have : z i = -1 := by linear_combination h0
  have := hz i
  simp_all

omit [Fintype ι] in
/-- Splitting off two distinct variables in a product over a finite set. -/
theorem prod_ite_ite_eq {k l : ι} (hkl : k ≠ l) (z : ι → ℂ) (u₁ u₂ : ℂ) (S : Finset ι) :
    ∏ i ∈ S, (if i = k then u₁ else if i = l then u₂ else z i) =
      (∏ i ∈ S, if i = k ∨ i = l then 1 else z i) * (if k ∈ S then u₁ else 1) *
        (if l ∈ S then u₂ else 1) := by
  have : ∀ i, (if i = k then u₁ else if i = l then u₂ else z i) =
      (if i = k ∨ i = l then 1 else z i) * (if i = k then u₁ else 1) *
        (if i = l then u₂ else 1) := by
    intro i
    by_cases hik : i = k
    · subst hik
      simp [hkl]
    · by_cases hil : i = l
      · subst hil
        simp [hik]
      · simp [hik, hil]
  rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']

/-- Bilinear decomposition of a multiaffine polynomial in two distinct variables, together with
the effect of multiplying the coefficients by a crossing factor. -/
theorem exists_bilinear_decomposition (w : Finset ι → ℂ) {k l : ι} (hkl : k ≠ l) (c : ℂ)
    (z : ι → ℂ) :
    ∃ A B C D : ℂ, ∀ u₁ u₂ : ℂ,
      ∑ S : Finset ι, w S * ∏ i ∈ S, (if i = k then u₁ else if i = l then u₂ else z i) =
          A + B * u₁ + C * u₂ + D * (u₁ * u₂) ∧
        ∑ S : Finset ι, (if (k ∈ S ↔ l ∈ S) then 1 else c) * w S *
            ∏ i ∈ S, (if i = k then u₁ else if i = l then u₂ else z i) =
          A + c * B * u₁ + c * C * u₂ + D * (u₁ * u₂) := by
  set m : Finset ι → ℂ := fun S => ∏ i ∈ S, if i = k ∨ i = l then 1 else z i with hm
  refine ⟨∑ S : Finset ι, (if k ∈ S then 0 else if l ∈ S then 0 else w S * m S),
    ∑ S : Finset ι, (if k ∈ S then (if l ∈ S then 0 else w S * m S) else 0),
    ∑ S : Finset ι, (if k ∈ S then 0 else if l ∈ S then w S * m S else 0),
    ∑ S : Finset ι, (if k ∈ S then (if l ∈ S then w S * m S else 0) else 0),
    fun u₁ u₂ => ⟨?_, ?_⟩⟩
  · simp only [prod_ite_ite_eq hkl, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hk : k ∈ S <;> by_cases hl : l ∈ S <;> simp [hk, hl, hm] <;> ring
  · simp only [prod_ite_ite_eq hkl, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hk : k ∈ S <;> by_cases hl : l ∈ S <;> simp [hk, hl, hm] <;> ring

/-- Multiplying the coefficients by a Lee–Yang crossing factor `c` (applied when exactly one of
`k ≠ l` lies in `S`) preserves nonvanishing on the open unit polydisc, for real `|c| ≤ 1`. -/
theorem PolydiscNonvanishing.mul_crossing {w : Finset ι → ℂ} (hw : PolydiscNonvanishing w)
    {k l : ι} (hkl : k ≠ l) {c : ℝ} (hc : |c| ≤ 1) :
    PolydiscNonvanishing fun S => (if (k ∈ S ↔ l ∈ S) then 1 else (c : ℂ)) * w S := by
  intro z hz
  obtain ⟨A, B, C, D, h⟩ := exists_bilinear_decomposition w hkl (c : ℂ) z
  have hy : ∀ u₁ u₂ : ℂ, ‖u₁‖ < 1 → ‖u₂‖ < 1 →
      ∀ i, ‖(if i = k then u₁ else if i = l then u₂ else z i)‖ < 1 := by
    intro u₁ u₂ h₁ h₂ i
    split_ifs
    exacts [h₁, h₂, hz i]
  have hyz : (fun i => if i = k then z k else if i = l then z l else z i) = z := by
    funext i
    split_ifs with h₁ h₂
    · rw [h₁]
    · rw [h₂]
    · rfl
  have key := edge_contraction hc (A := A) (B := B) (C := C) (D := D)
    (fun u₁ u₂ h₁ h₂ => by rw [← (h u₁ u₂).1]; exact hw _ (hy u₁ u₂ h₁ h₂)) (hz k) (hz l)
  have e := (h (z k) (z l)).2
  rw [hyz] at e
  rwa [e]

/-- A product of crossing factors between a fixed vertex `v` and the vertices of `T ∌ v`
preserves nonvanishing on the open unit polydisc. -/
theorem PolydiscNonvanishing.prod_crossing {w : Finset ι → ℂ} (hw : PolydiscNonvanishing w)
    {v : ι} (c : ι → ℝ) (T : Finset ι) (hv : v ∉ T) (hc : ∀ j ∈ T, |c j| ≤ 1) :
    PolydiscNonvanishing fun S =>
      (∏ j ∈ T, if (v ∈ S ↔ j ∈ S) then 1 else (c j : ℂ)) * w S := by
  induction T using Finset.induction_on with
  | empty => simpa using hw
  | insert j T hjT ih =>
    have hvj : v ≠ j := fun h => hv (h ▸ Finset.mem_insert_self j T)
    have := (ih (fun h => hv (Finset.mem_insert_of_mem h))
      (fun i hi => hc i (Finset.mem_insert_of_mem hi))).mul_crossing hvj
      (hc j (Finset.mem_insert_self j T))
    convert this using 2 with S
    rw [Finset.prod_insert hjT]
    ring

/-- The Lee–Yang weight of `S`, restricted to interactions within `T`. -/
def weight (a : ι → ι → ℝ) (T S : Finset ι) : ℂ :=
  ∏ i ∈ T, ∏ j ∈ T, if i ∈ S ∧ j ∉ S then (a i j : ℂ) else 1

omit [Fintype ι] in
/-- Adding a vertex `v ∉ T` multiplies the weight by the crossing factors between `v` and `T`. -/
theorem weight_insert {a : ι → ι → ℝ} (ha : ∀ i j, a i j = a j i) {v : ι} {T : Finset ι}
    (hv : v ∉ T) (S : Finset ι) :
    weight a (insert v T) S =
      (∏ j ∈ T, if (v ∈ S ↔ j ∈ S) then 1 else (a v j : ℂ)) * weight a T S := by
  have hcross : ∀ j, (if (v ∈ S ↔ j ∈ S) then 1 else (a v j : ℂ)) =
      (if v ∈ S ∧ j ∉ S then (a v j : ℂ) else 1) *
        (if j ∈ S ∧ v ∉ S then (a j v : ℂ) else 1) := by
    intro j
    by_cases hvS : v ∈ S <;> by_cases hjS : j ∈ S <;> simp [hvS, hjS, ha j v]
  simp only [weight]
  rw [Finset.prod_insert hv, Finset.prod_insert hv,
    Finset.prod_congr rfl fun i _ => Finset.prod_insert hv, Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun j _ => hcross j, Finset.prod_mul_distrib]
  simp only [and_not_self, ↓reduceIte, one_mul]
  ring

/-- The Lee–Yang weights restricted to any vertex set `T` give a polynomial without zeros on the
open unit polydisc. -/
theorem polydiscNonvanishing_weight {a : ι → ι → ℝ} (ha : ∀ i j, a i j = a j i)
    (h1 : ∀ i j, |a i j| ≤ 1) (T : Finset ι) : PolydiscNonvanishing (weight a T) := by
  induction T using Finset.induction_on with
  | empty =>
    convert (polydiscNonvanishing_one : PolydiscNonvanishing fun _ : Finset ι => (1 : ℂ))
      using 1
    funext S
    simp [weight]
  | insert v T hvT ih =>
    have := ih.prod_crossing (a v) T hvT fun j _ => h1 v j
    convert this using 1
    funext S
    exact weight_insert ha hvT S

/-- On the full vertex set, the weight is `∏ i ∈ S, ∏ j ∈ Sᶜ, a i j`. -/
theorem weight_univ (a : ι → ι → ℝ) (S : Finset ι) :
    weight a univ S = ∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ) := by
  have h1 : ∀ i, (∏ j, if i ∈ S ∧ j ∉ S then (a i j : ℂ) else 1) =
      if i ∈ S then ∏ j ∈ Sᶜ, (a i j : ℂ) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, true_and, ↓reduceIte]
      rw [← Finset.prod_filter]
      congr 1
      ext j
      simp
    · simp [hi]
  simp only [weight, h1]
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp

/-! ### The Lee–Yang theorem -/

/-- **Lee–Yang circle theorem**, polydisc form (Lee–Yang 1952, via Asano 1970).
For a real symmetric matrix `a` with `|a i j| ≤ 1`, the Lee–Yang polynomial has no zero on the
open unit polydisc. -/
theorem lee_yang_polydisc {a : ι → ι → ℝ} (ha : ∀ i j, a i j = a j i)
    (h1 : ∀ i j, |a i j| ≤ 1) {z : ι → ℂ} (hz : ∀ i, ‖z i‖ < 1) :
    ∑ S : Finset ι, (∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ)) * ∏ i ∈ S, z i ≠ 0 := by
  have := polydiscNonvanishing_weight ha h1 univ z hz
  simpa only [weight_univ] using this

/-- The Lee–Yang weights are invariant under complementation, for symmetric `a`. -/
theorem prod_prod_compl_compl {a : ι → ι → ℝ} (ha : ∀ i j, a i j = a j i) (S : Finset ι) :
    ∏ i ∈ Sᶜ, ∏ j ∈ Sᶜᶜ, (a i j : ℂ) = ∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ) := by
  rw [compl_compl, Finset.prod_comm]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by rw [ha]

/-- The Lee–Yang polynomial is palindromic: `P(z) = (∏ i, z i) * P(z⁻¹)`. -/
theorem sum_eq_prod_mul_sum_inv {a : ι → ι → ℝ} (ha : ∀ i j, a i j = a j i) {z : ι → ℂ}
    (hz : ∀ i, z i ≠ 0) :
    ∑ S : Finset ι, (∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ)) * ∏ i ∈ S, z i =
      (∏ i, z i) * ∑ S : Finset ι, (∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ)) * ∏ i ∈ S, (z i)⁻¹ := by
  have hS : ∀ S : Finset ι,
      (∏ i, z i) * ((∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ)) * ∏ i ∈ S, (z i)⁻¹) =
        (∏ i ∈ Sᶜ, ∏ j ∈ Sᶜᶜ, (a i j : ℂ)) * ∏ i ∈ Sᶜ, z i := by
    intro S
    have h2 : (∏ i ∈ S, z i) * ∏ i ∈ S, (z i)⁻¹ = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hz i)
    rw [prod_prod_compl_compl ha S, ← Finset.prod_mul_prod_compl S z]
    linear_combination ((∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ)) * ∏ i ∈ Sᶜ, z i) * h2
  rw [Finset.mul_sum, Finset.sum_congr rfl fun S _ => hS S]
  let e : Finset ι ≃ Finset ι := ⟨compl, compl, compl_compl, compl_compl⟩
  exact (Equiv.sum_comp e fun S => (∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ)) * ∏ i ∈ S, z i).symm

/-- **Lee–Yang theorem**, exterior form: the Lee–Yang polynomial has no zero when every
`‖z i‖ > 1`. -/
theorem lee_yang_exterior {a : ι → ι → ℝ} (ha : ∀ i j, a i j = a j i)
    (h1 : ∀ i j, |a i j| ≤ 1) {z : ι → ℂ} (hz : ∀ i, 1 < ‖z i‖) :
    ∑ S : Finset ι, (∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ)) * ∏ i ∈ S, z i ≠ 0 := by
  have hz0 : ∀ i, z i ≠ 0 := fun i h => by
    have := hz i
    rw [h, norm_zero] at this
    linarith
  rw [sum_eq_prod_mul_sum_inv ha hz0]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hz0 i)
    (lee_yang_polydisc ha h1 fun i => ?_)
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ (hz i)

/-- **Lee–Yang circle theorem** (Lee–Yang 1952). For a real symmetric matrix `a` with
`|a i j| ≤ 1`, every zero of `z ↦ ∑ S, (∏ i ∈ S, ∏ j ∈ Sᶜ, a i j) * z ^ #S` lies on the unit
circle. -/
theorem lee_yang_circle {a : ι → ι → ℝ} (ha : ∀ i j, a i j = a j i)
    (h1 : ∀ i j, |a i j| ≤ 1) {z : ℂ}
    (hz : ∑ S : Finset ι, (∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ)) * z ^ S.card = 0) : ‖z‖ = 1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact lee_yang_polydisc ha h1 (z := fun _ => z) (fun _ => hlt)
      (by simpa only [Finset.prod_const] using hz)
  · exact lee_yang_exterior ha h1 (z := fun _ => z) (fun _ => hgt)
      (by simpa only [Finset.prod_const] using hz)

/-- **Lee–Yang circle theorem**, polynomial form: every root of the one-variable Lee–Yang
polynomial lies on the unit circle. -/
theorem norm_eq_one_of_mem_roots {a : ι → ι → ℝ} (ha : ∀ i j, a i j = a j i)
    (h1 : ∀ i j, |a i j| ≤ 1) {z : ℂ}
    (hz : z ∈ (∑ S : Finset ι, Polynomial.C (∏ i ∈ S, ∏ j ∈ Sᶜ, (a i j : ℂ)) *
      Polynomial.X ^ S.card).roots) : ‖z‖ = 1 := by
  have := Polynomial.isRoot_of_mem_roots hz
  rw [Polynomial.IsRoot.def, Polynomial.eval_finsetSum] at this
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at this
  exact lee_yang_circle ha h1 this

/-- **Lee–Yang theorem for the ferromagnetic Ising model.** With couplings `J i j ≥ 0` and inverse
temperature `β ≥ 0`, the zeros of the partition function in the fugacity `z` (with
`a i j = exp (-2 β J i j)`) lie on the unit circle. -/
theorem ising_norm_eq_one {J : ι → ι → ℝ} (hJ : ∀ i j, J i j = J j i)
    (hJ0 : ∀ i j, 0 ≤ J i j) {β : ℝ} (hβ : 0 ≤ β) {z : ℂ}
    (hz : ∑ S : Finset ι,
      (∏ i ∈ S, ∏ j ∈ Sᶜ, (Real.exp (-2 * β * J i j) : ℂ)) * z ^ S.card = 0) :
    ‖z‖ = 1 := by
  refine lee_yang_circle (a := fun i j => Real.exp (-2 * β * J i j)) (fun i j => by rw [hJ])
    (fun i j => ?_) hz
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have := mul_nonneg hβ (hJ0 i j)
  linarith

end RealRooted.LeeYang
