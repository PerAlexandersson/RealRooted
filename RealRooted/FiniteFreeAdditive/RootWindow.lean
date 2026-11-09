module

public import RealRooted.Basic.Coefficients
public import RealRooted.FiniteFreeAdditive
public import RealRooted.RootLocation.Basic
import RealRooted.FiniteFreeAdditive.Preservation
import RealRooted.Linear
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Root windows for the finite-free additive convolution

We prove the classical location theorem for the finite-free additive convolution of
Marcus--Spielman--Srivastava: if `p` and `q` have degree `d` and all roots of `p` lie in
`[A, B]` and all roots of `q` lie in `[a, b]`, then all roots of
`finiteFreeAdditiveConvolution d p q` lie in `[A + a, B + b]`.  The ray versions (roots in
`Iic B` and `Iic b` give roots in `Iic (B + b)`, and the mirror statement for `Ici`) are proved
first.  This is Walsh's coincidence-type location theorem (Walsh 1922) in the finite-free
setting; see Leake--Ryder, "On the further structure of the finite free convolutions",
Proposition 1.1.

The proof uses the following ingredients.

* The convolution has the differential expression
  `p ⊞_d q = ∑ i, ((d - i)! / d!) p_{d-i} q^{(i)}`, which shows that it is covariant under
  translations of the variable: `(p(x + s)) ⊞_d (q(x + t)) = (p ⊞_d q)(x + s + t)`.
* It is covariant under reflection `x ↦ -x`, up to the sign `(-1)^d`.
* It preserves nonnegativity of coefficients, since its weights are nonnegative.
* A polynomial with positive leading coefficient and only nonpositive real roots has
  nonnegative coefficients, and a polynomial with nonnegative coefficients has no positive root.
-/

public section

open Polynomial Set

namespace RealRooted

noncomputable section

/-! ### Linearity -/

/-- The convolution coefficient is homogeneous in the left argument. -/
theorem finiteFreeAdditiveConvolutionCoeff_C_mul_left (d k : ℕ) (c : ℝ) (p q : ℝ[X]) :
    finiteFreeAdditiveConvolutionCoeff d (C c * p) q k =
      c * finiteFreeAdditiveConvolutionCoeff d p q k := by
  simp only [finiteFreeAdditiveConvolutionCoeff, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The convolution coefficient is homogeneous in the right argument. -/
theorem finiteFreeAdditiveConvolutionCoeff_C_mul_right (d k : ℕ) (c : ℝ) (p q : ℝ[X]) :
    finiteFreeAdditiveConvolutionCoeff d p (C c * q) k =
      c * finiteFreeAdditiveConvolutionCoeff d p q k := by
  simp only [finiteFreeAdditiveConvolutionCoeff, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Finite-free additive convolution is homogeneous in the left argument. -/
theorem finiteFreeAdditiveConvolution_C_mul_left (d : ℕ) (c : ℝ) (p q : ℝ[X]) :
    finiteFreeAdditiveConvolution d (C c * p) q = C c * finiteFreeAdditiveConvolution d p q := by
  ext j
  rw [coeff_C_mul, coeff_finiteFreeAdditiveConvolution, coeff_finiteFreeAdditiveConvolution]
  split_ifs
  · exact finiteFreeAdditiveConvolutionCoeff_C_mul_left _ _ _ _ _
  · simp

/-- Finite-free additive convolution is homogeneous in the right argument. -/
theorem finiteFreeAdditiveConvolution_C_mul_right (d : ℕ) (c : ℝ) (p q : ℝ[X]) :
    finiteFreeAdditiveConvolution d p (C c * q) = C c * finiteFreeAdditiveConvolution d p q := by
  rw [finiteFreeAdditiveConvolution_comm, finiteFreeAdditiveConvolution_C_mul_left,
    finiteFreeAdditiveConvolution_comm]

/-! ### Differential expression and translation covariance -/

/-- The finite-free additive weight written with a descending factorial: the factor of the
differential operator expression. -/
theorem finiteFreeAdditiveConvolutionGamma_eq_factorial_mul_descFactorial (d i l : ℕ)
    (hil : i + l ≤ d) :
    finiteFreeAdditiveConvolutionGamma d i l =
      ((d - i).factorial : ℝ) / d.factorial * ((d - l).descFactorial i : ℝ) := by
  have h : (d - l - i).factorial * (d - l).descFactorial i = (d - l).factorial :=
    Nat.factorial_mul_descFactorial (by lia)
  have h' : ((d - l - i).factorial : ℝ) * ((d - l).descFactorial i : ℝ) =
      (d - l).factorial := by exact_mod_cast h
  have hsub : d - i - l = d - l - i := by lia
  unfold finiteFreeAdditiveConvolutionGamma
  rw [hsub, ← h']
  have : ((d - l - i).factorial : ℝ) ≠ 0 := by positivity
  have : (d.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Inside the degree box, the finite-free additive convolution is the differential operator
`∑ i, ((d - i)! / d!) p_{d-i} ∂^i` applied to the second argument. -/
theorem finiteFreeAdditiveConvolution_eq_sum_iterate_derivative (d : ℕ) (p : ℝ[X]) {q : ℝ[X]}
    (hq : q.natDegree ≤ d) :
    finiteFreeAdditiveConvolution d p q =
      ∑ i ∈ Finset.range (d + 1),
        C (((d - i).factorial : ℝ) / d.factorial * p.coeff (d - i)) * derivative^[i] q := by
  ext j
  rw [finsetSum_coeff, coeff_finiteFreeAdditiveConvolution]
  simp only [coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul]
  split_ifs with hj
  · obtain ⟨k, rfl⟩ : ∃ k, k + j = d := ⟨d - j, by lia⟩
    rw [Nat.add_sub_cancel, finiteFreeAdditiveConvolutionCoeff]
    refine Eq.trans ?_ (Finset.sum_subset (s₁ := Finset.range (k + 1))
      (Finset.range_subset_range.2 (show k + 1 ≤ k + j + 1 by lia)) ?_)
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := by simpa [Nat.lt_succ_iff] using hi
      rw [finiteFreeAdditiveConvolutionGamma_eq_factorial_mul_descFactorial _ _ _ (by lia)]
      have hdk : k + j - (k - i) = j + i := by lia
      rw [hdk]
      ring
    · intro i _ hi
      rw [Finset.mem_range] at hi
      rw [coeff_eq_zero_of_natDegree_lt (p := q) (n := j + i) (by lia)]
      simp
  · refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [coeff_eq_zero_of_natDegree_lt (p := q) (n := j + i) (by lia)]
    simp

private theorem iterate_derivative_comp_X_add_C (q : ℝ[X]) (t : ℝ) (i : ℕ) :
    derivative^[i] (q.comp (X + C t)) = (derivative^[i] q).comp (X + C t) := by
  induction i with
  | zero => rfl
  | succ i ih => simp [Function.iterate_succ_apply', ih, derivative_comp]

private theorem natDegree_comp_X_add_C_le {q : ℝ[X]} {d : ℕ} (hq : q.natDegree ≤ d) (t : ℝ) :
    (q.comp (X + C t)).natDegree ≤ d := by
  simpa [natDegree_comp] using hq

/-- Translating the second argument translates the convolution. -/
theorem finiteFreeAdditiveConvolution_comp_X_add_C_right (d : ℕ) (p : ℝ[X]) {q : ℝ[X]}
    (hq : q.natDegree ≤ d) (t : ℝ) :
    finiteFreeAdditiveConvolution d p (q.comp (X + C t)) =
      (finiteFreeAdditiveConvolution d p q).comp (X + C t) := by
  rw [finiteFreeAdditiveConvolution_eq_sum_iterate_derivative d p hq,
    finiteFreeAdditiveConvolution_eq_sum_iterate_derivative d p (natDegree_comp_X_add_C_le hq t),
    Polynomial.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [C_mul_comp, iterate_derivative_comp_X_add_C]

/-- Translating the first argument translates the convolution. -/
theorem finiteFreeAdditiveConvolution_comp_X_add_C_left (d : ℕ) {p : ℝ[X]} (q : ℝ[X])
    (hp : p.natDegree ≤ d) (s : ℝ) :
    finiteFreeAdditiveConvolution d (p.comp (X + C s)) q =
      (finiteFreeAdditiveConvolution d p q).comp (X + C s) := by
  rw [finiteFreeAdditiveConvolution_comm, finiteFreeAdditiveConvolution_comp_X_add_C_right d q hp,
    finiteFreeAdditiveConvolution_comm]

/-- **Translation covariance.**  Translating the arguments of the degree-`d` finite-free additive
convolution by `s` and `t` translates the convolution by `s + t`. -/
theorem finiteFreeAdditiveConvolution_comp_X_add_C {d : ℕ} {p q : ℝ[X]} (hp : p.natDegree ≤ d)
    (hq : q.natDegree ≤ d) (s t : ℝ) :
    finiteFreeAdditiveConvolution d (p.comp (X + C s)) (q.comp (X + C t)) =
      (finiteFreeAdditiveConvolution d p q).comp (X + C (s + t)) := by
  rw [finiteFreeAdditiveConvolution_comp_X_add_C_left d _ hp,
    finiteFreeAdditiveConvolution_comp_X_add_C_right d p hq, comp_assoc]
  simp [add_assoc, map_add]

/-! ### Reflection -/

/-- **Reflection covariance.**  Reflecting both arguments of the degree-`d` finite-free additive
convolution reflects the convolution, up to the sign `(-1) ^ d`. -/
theorem finiteFreeAdditiveConvolution_comp_neg_X (d : ℕ) (p q : ℝ[X]) :
    finiteFreeAdditiveConvolution d (p.comp (-X)) (q.comp (-X)) =
      C ((-1 : ℝ) ^ d) * (finiteFreeAdditiveConvolution d p q).comp (-X) := by
  ext j
  rw [coeff_C_mul, coeff_comp_neg_X, coeff_finiteFreeAdditiveConvolution,
    coeff_finiteFreeAdditiveConvolution]
  split_ifs with hj
  · simp only [finiteFreeAdditiveConvolutionCoeff, coeff_comp_neg_X, Finset.sum_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ d - j := by simpa [Nat.lt_succ_iff] using hi
    have hpow : ((-1 : ℝ) ^ (d - i)) * (-1) ^ (d - (d - j - i)) = (-1) ^ d * (-1) ^ j := by
      rw [← pow_add, ← pow_add]
      congr 1
      lia
    calc _ = finiteFreeAdditiveConvolutionGamma d i (d - j - i) * p.coeff (d - i) *
            q.coeff (d - (d - j - i)) * ((-1 : ℝ) ^ (d - i) * (-1) ^ (d - (d - j - i))) := by
          ring
      _ = _ := by rw [hpow]; ring
  · simp

/-! ### Nonnegativity -/

/-- The finite-free additive convolution weights are nonnegative. -/
theorem finiteFreeAdditiveConvolutionGamma_nonneg (d i j : ℕ) :
    0 ≤ finiteFreeAdditiveConvolutionGamma d i j := by
  unfold finiteFreeAdditiveConvolutionGamma
  positivity

/-- The finite-free additive convolution of polynomials with nonnegative coefficients has
nonnegative coefficients. -/
theorem HasNonnegCoeffs.finiteFreeAdditiveConvolution {p q : ℝ[X]} (hp : HasNonnegCoeffs p)
    (hq : HasNonnegCoeffs q) (d : ℕ) : HasNonnegCoeffs (finiteFreeAdditiveConvolution d p q) := by
  intro n
  rw [coeff_finiteFreeAdditiveConvolution]
  split_ifs
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (finiteFreeAdditiveConvolutionGamma_nonneg _ _ _) (hp _)) (hq _)
  · exact le_rfl

/-! ### Root windows -/

/-- The core of the upper ray bound: positive leading coefficients, exact degree `d`. -/
private theorem forall_roots_le_finiteFreeAdditiveConvolution_of_pos {d : ℕ} {p q : ℝ[X]} {B b : ℝ}
    (hpd : p.natDegree = d) (hqd : q.natDegree = d) (hp0 : HasPosLeadingCoeff p)
    (hq0 : HasPosLeadingCoeff q) (hps : p.Splits) (hqs : q.Splits)
    (hpB : ∀ r ∈ p.roots, r ≤ B) (hqb : ∀ r ∈ q.roots, r ≤ b) :
    ∀ r ∈ (finiteFreeAdditiveConvolution d p q).roots, r ≤ B + b := by
  have hshift : ∀ {f : ℝ[X]} {c : ℝ}, HasPosLeadingCoeff f → f.Splits → (∀ r ∈ f.roots, r ≤ c) →
      HasNonnegCoeffs (f.comp (X + C c)) := by
    intro f c hf0 hfs hfc
    refine ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos (hfs.comp_X_add_C c)).2
      ⟨hf0.comp_X_add_C c, ?_⟩).1
    intro s hs
    rw [roots_comp_X_add_C] at hs
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hs
    linarith [hfc t ht]
  have hnn := (hshift hp0 hps hpB).finiteFreeAdditiveConvolution (hshift hq0 hqs hqb) d
  rw [finiteFreeAdditiveConvolution_comp_X_add_C hpd.le hqd.le] at hnn
  intro r hr
  have hroot := roots_nonpos_of_hasNonnegCoeffs hnn (r - (B + b)) (by
    rw [roots_comp_X_add_C]
    exact Multiset.mem_map.2 ⟨r, hr, rfl⟩)
  linarith

/-- **Upper ray bound.**  If `p` and `q` have degree `d` and all roots of `p` (resp. `q`) are at
most `B` (resp. `b`), then all roots of `p ⊞_d q` are at most `B + b`.  The conclusion is stated
for the multiset of roots, there is no sign assumption on the leading coefficients. -/
theorem forall_roots_le_finiteFreeAdditiveConvolution {d : ℕ} {p q : ℝ[X]} {B b : ℝ}
    (hpd : p.natDegree = d) (hqd : q.natDegree = d) (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hps : p.Splits) (hqs : q.Splits)
    (hpB : ∀ r ∈ p.roots, r ≤ B) (hqb : ∀ r ∈ q.roots, r ≤ b) :
    ∀ r ∈ (finiteFreeAdditiveConvolution d p q).roots, r ≤ B + b := by
  set a := p.leadingCoeff with ha
  set e := q.leadingCoeff with he
  have ha0 : a ≠ 0 := leadingCoeff_ne_zero.2 hp0
  have he0 : e ≠ 0 := leadingCoeff_ne_zero.2 hq0
  have hconv : finiteFreeAdditiveConvolution d (C a * p) (C e * q) =
      C (a * e) * finiteFreeAdditiveConvolution d p q := by
    rw [finiteFreeAdditiveConvolution_C_mul_left, finiteFreeAdditiveConvolution_C_mul_right,
      ← mul_assoc, ← C_mul]
  have hpos : ∀ {f : ℝ[X]}, f ≠ 0 → HasPosLeadingCoeff (C f.leadingCoeff * f) := by
    intro f hf
    have := leadingCoeff_ne_zero.2 hf
    simpa [HasPosLeadingCoeff, leadingCoeff_mul] using mul_self_pos.2 this
  have key := forall_roots_le_finiteFreeAdditiveConvolution_of_pos (d := d) (B := B) (b := b)
    (by rwa [natDegree_C_mul ha0]) (by rwa [natDegree_C_mul he0]) (hpos hp0) (hpos hq0)
    ((Splits.C a).mul hps) ((Splits.C e).mul hqs)
    (by rwa [roots_C_mul _ ha0]) (by rwa [roots_C_mul _ he0])
  rwa [hconv, roots_C_mul _ (mul_ne_zero ha0 he0)] at key

/-- **Walsh's upper ray bound for the finite-free additive convolution.**  If `p` and `q` have
degree `d` and are rooted in `(-∞, B]` and `(-∞, b]`, then `p ⊞_d q` is rooted in `(-∞, B + b]`.
See Leake--Ryder, Proposition 1.1. -/
theorem IsRealRootedIn.finiteFreeAdditiveConvolution_Iic {d : ℕ} {p q : ℝ[X]} {B b : ℝ}
    (hpd : p.natDegree = d) (hqd : q.natDegree = d) (hp : IsRealRootedIn (Iic B) p)
    (hq : IsRealRootedIn (Iic b) q) :
    IsRealRootedIn (Iic (B + b)) (finiteFreeAdditiveConvolution d p q) :=
  ⟨finiteFreeAdditiveConvolution_ne_zero_of_natDegree_eq d hpd hqd hp.ne_zero hq.ne_zero,
    splits_finiteFreeAdditiveConvolution d hp.splits hq.splits hpd.le hqd.le,
    forall_roots_le_finiteFreeAdditiveConvolution hpd hqd hp.ne_zero hq.ne_zero hp.splits
      hq.splits (fun _ hr => hp.mem_of_mem_roots hr) (fun _ hr => hq.mem_of_mem_roots hr)⟩

private theorem IsRealRootedIn.comp_neg_X_Ici {A : ℝ} {p : ℝ[X]} (h : IsRealRootedIn (Ici A) p) :
    IsRealRootedIn (Iic (-A)) (p.comp (-X)) := by
  have := h.comp_C_mul_X_add_C 0 (neg_ne_zero.2 one_ne_zero)
  simp only [map_neg, map_one, neg_mul, one_mul, map_zero, add_zero] at this
  refine this.mono fun x hx => ?_
  simp only [mem_preimage, mem_Ici, mem_Iic] at hx ⊢
  linarith

/-- **Walsh's lower ray bound for the finite-free additive convolution.**  If `p` and `q` have
degree `d` and are rooted in `[A, ∞)` and `[a, ∞)`, then `p ⊞_d q` is rooted in `[A + a, ∞)`.
See Leake--Ryder, Proposition 1.1. -/
theorem IsRealRootedIn.finiteFreeAdditiveConvolution_Ici {d : ℕ} {p q : ℝ[X]} {A a : ℝ}
    (hpd : p.natDegree = d) (hqd : q.natDegree = d) (hp : IsRealRootedIn (Ici A) p)
    (hq : IsRealRootedIn (Ici a) q) :
    IsRealRootedIn (Ici (A + a)) (finiteFreeAdditiveConvolution d p q) := by
  have hmain := IsRealRootedIn.finiteFreeAdditiveConvolution_Iic (d := d)
    (by rw [natDegree_comp_neg_X, hpd]) (by rw [natDegree_comp_neg_X, hqd]) hp.comp_neg_X_Ici
    hq.comp_neg_X_Ici
  rw [finiteFreeAdditiveConvolution_comp_neg_X] at hmain
  refine ⟨finiteFreeAdditiveConvolution_ne_zero_of_natDegree_eq d hpd hqd hp.ne_zero hq.ne_zero,
    splits_finiteFreeAdditiveConvolution d hp.splits hq.splits hpd.le hqd.le, fun r hr => ?_⟩
  have hroot := hmain.mem_of_isRoot (r := -r) (by
    have hr' := (mem_roots (finiteFreeAdditiveConvolution_ne_zero_of_natDegree_eq d hpd hqd
      hp.ne_zero hq.ne_zero)).1 hr
    simp [IsRoot.def, eval_comp, hr'.eq_zero])
  simp only [mem_Iic] at hroot
  simp only [mem_Ici]
  linarith

/-- **Walsh's coincidence-type window for the finite-free additive convolution.**  If `p` and `q`
have degree `d`, `p` is rooted in `[A, B]` and `q` is rooted in `[a, b]`, then `p ⊞_d q` is
rooted in `[A + a, B + b]`.  See Leake--Ryder, "On the further structure of the finite free
convolutions", Proposition 1.1, and Walsh (1922). -/
theorem IsRealRootedIn.finiteFreeAdditiveConvolution_Icc {d : ℕ} {p q : ℝ[X]} {A B a b : ℝ}
    (hpd : p.natDegree = d) (hqd : q.natDegree = d) (hp : IsRealRootedIn (Icc A B) p)
    (hq : IsRealRootedIn (Icc a b) q) :
    IsRealRootedIn (Icc (A + a) (B + b)) (finiteFreeAdditiveConvolution d p q) := by
  have h1 := IsRealRootedIn.finiteFreeAdditiveConvolution_Ici hpd hqd
    (hp.mono Icc_subset_Ici_self) (hq.mono Icc_subset_Ici_self)
  have h2 := IsRealRootedIn.finiteFreeAdditiveConvolution_Iic hpd hqd
    (hp.mono Icc_subset_Iic_self) (hq.mono Icc_subset_Iic_self)
  exact (h1.inter h2).mono fun x hx => ⟨hx.1, hx.2⟩

end

end RealRooted
