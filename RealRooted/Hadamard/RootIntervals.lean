module

public import RealRooted.Hadamard.Basic
public import RealRooted.RootLocation.Basic
import RealRooted.DegreeDropReversal
import RealRooted.Hadamard.Grace
import RealRooted.Hadamard.SchurSzegoSigns
import RealRooted.Mathlib.Algebra.Polynomial.Reverse
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots
import RealRooted.ObreschkoffConverse.DegreeGap
import RealRooted.SameDegreeDerivative
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Root intervals of Schur--Szegő compositions

Kostov--Shapiro: if `G` has exact degree `D` and its roots lie in `[-b, -a]` with `0 < a ≤ b`, and
`f` has exact degree `D` with roots in `[-v, -u]`, `0 ≤ u ≤ v`, then the Schur--Szegő composition
`schurSzegoComp D f G` has all its roots in `[-(b v), -(a u)]`.

The upper bound `|root| ≤ b v` is Szegő's theorem that the roots of `f *_D G` are `-w β` with `w`
a root of `f` rotated in a disk and `β` a root of `G`; we derive it from Grace's apolarity theorem
for disks (`RealRooted.exists_apolarTwist_root_of_grace`).  The lower bound `|root| ≥ a u` follows
by reflecting both inputs (`RealRooted.reflect_schurSzegoComp`).  That the roots are real and
nonpositive is the finite Schur--Szegő theorem together with the Kostov--Shapiro sign counts.

## Main statements

* `RealRooted.norm_le_mul_of_isRoot_map_schurSzegoComp`: the complex Szegő bound.
* `RealRooted.IsRealRootedIn.schurSzegoComp_Icc`: the root interval `[-(b v), -(a u)]` of `f *_D G`.
* `RealRooted.IsRealRootedIn.schurSzegoComp_Icc_of_natDegree_le`: the same interval for inputs of
  degree at most `D`.
* `RealRooted.IsRealRootedIn.schurSzegoComp_Icc_zero`: the ray version `[-(b v), 0]`, where the
  roots of the inputs may touch `0`, by a limit argument.
* `RealRooted.IsRealRootedIn.schurSzegoComp_Icc_zero_of_natDegree_le`: the lower-degree ray
  version, allowing zero output.

## References

* V. Kostov, B. Shapiro, *On the Schur--Szegő composition of polynomials*, C. R. Acad. Sci.
  Paris 343 (2006), Theorem 1.1 and Proposition 1.2.
-/

public section

open Polynomial Set Filter Topology

noncomputable section

namespace RealRooted

/-- **Szegő's root bound.**  Let `f` and `g` be real polynomials of degree `D`, with `g 0 ≠ 0`.
If every complex root of `f` has norm at most `v` and every complex root of `g` has norm at most
`b`, then every complex root of `schurSzegoComp D f g` has norm at most `b * v`.

By Grace's apolarity theorem for disks, a root `z` of the composition is `-w μ` for a root `μ` of
`g` and a point `w` in the disk of radius `v`. -/
theorem norm_le_mul_of_isRoot_map_schurSzegoComp {D : ℕ} {f g : ℝ[X]} {v b : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hfdeg : f.natDegree = D) (hgdeg : g.natDegree = D)
    (hg0 : g.coeff 0 ≠ 0)
    (hf : ∀ w : ℂ, (f.map Complex.ofRealHom).IsRoot w → ‖w‖ ≤ v)
    (hg : ∀ μ : ℂ, (g.map Complex.ofRealHom).IsRoot μ → ‖μ‖ ≤ b)
    {z : ℂ} (hz : ((schurSzegoComp D f g).map Complex.ofRealHom).IsRoot z) :
    ‖z‖ ≤ b * v := by
  by_cases hz0 : z = 0
  · simpa [hz0] using mul_nonneg hb hv
  have hfmap : (f.map Complex.ofRealHom).natDegree = D := by
    rw [natDegree_map_eq_of_injective Complex.ofReal_injective, hfdeg]
  have hgmap : (g.map Complex.ofRealHom).natDegree = D := by
    rw [natDegree_map_eq_of_injective Complex.ofReal_injective, hgdeg]
  obtain ⟨F₀, hF⟩ := exists_binomialLift_eq (f.map Complex.ofRealHom) hfmap.le
  obtain ⟨G₀, hG⟩ := exists_binomialLift_eq (g.map Complex.ofRealHom) hgmap.le
  have hsum : ∑ k ∈ Finset.range (D + 1),
      (Nat.choose D k : ℂ) * F₀.coeff k * G₀.coeff k * z ^ k = 0 := by
    rw [← eval_map_schurSzegoComp_eq_sum D f g hF hG z]
    exact hz
  have hFdeg : (binomialLift D F₀).natDegree = D := by rw [hF, hfmap]
  have hg0c : (g.map Complex.ofRealHom).coeff 0 ≠ 0 := by simpa using hg0
  have hTwdeg : (binomialLift D (apolarTwist D z G₀)).natDegree = D :=
    natDegree_binomialLift_apolarTwist D z hG hg0c
  have hroots : (binomialLift D F₀).RootsIn (Metric.closedBall 0 v) := fun w hw => by
    rw [hF] at hw
    simpa using hf w hw
  obtain ⟨w, hwroot, hwmem⟩ := exists_apolarTwist_root_of_grace hv hFdeg hTwdeg hsum hroots
  have hGn : G₀.coeff D ≠ 0 := by
    have h : (g.map Complex.ofRealHom).coeff D ≠ 0 := by
      rw [← hgmap]
      exact leadingCoeff_ne_zero.mpr (fun h0 => by simp [h0] at hg0c)
    rwa [← hG, coeff_binomialLift, ite_eq_left le_rfl, Nat.choose_self, Nat.cast_one,
      one_mul] at h
  have hcoeff0 : (binomialLift D (apolarTwist D z G₀)).coeff 0 ≠ 0 := by
    rw [coeff_binomialLift, ite_eq_left (Nat.zero_le D), coeff_apolarTwist,
      ite_eq_left (Nat.zero_le D)]
    simp [hGn, hz0]
  have hwne : w ≠ 0 := by
    rintro rfl
    exact hcoeff0 (by simpa [Polynomial.coeff_zero_eq_eval_zero] using hwroot)
  have hμ : (binomialLift D G₀).IsRoot (-z / w) :=
    (isRoot_binomialLift_apolarTwist_iff D z G₀ hwne).mp hwroot
  rw [hG] at hμ
  have hμb := hg _ hμ
  have hwv : ‖w‖ ≤ v := by simpa using hwmem
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  rw [norm_div, norm_neg, div_le_iff₀ hwpos] at hμb
  exact hμb.trans (mul_le_mul_of_nonneg_left hwv hb)

/-- A complex root of a splitting nonzero real polynomial is a real root. -/
private theorem exists_eq_ofReal_of_isRoot_map {p : ℝ[X]} (hp0 : p ≠ 0) (hp : p.Splits) {w : ℂ}
    (hw : (p.map Complex.ofRealHom).IsRoot w) : ∃ r ∈ p.roots, w = (r : ℂ) := by
  obtain ⟨r, rfl⟩ : w ∈ Complex.ofRealHom.range := hp.mem_range_of_isRoot hp0 hw
  exact ⟨r, (mem_roots hp0).2 (hw.of_map Complex.ofReal_injective), rfl⟩

/-- Real version of `norm_le_mul_of_isRoot_map_schurSzegoComp`: every real root of
`schurSzegoComp D f g` has absolute value at most `b * v`. -/
theorem abs_le_mul_of_mem_roots_schurSzegoComp {D : ℕ} {f g : ℝ[X]} {v b : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hf0 : f ≠ 0) (hfs : f.Splits) (hgs : g.Splits)
    (hfdeg : f.natDegree = D) (hgdeg : g.natDegree = D) (hg0 : g.coeff 0 ≠ 0)
    (hf : ∀ r ∈ f.roots, |r| ≤ v) (hg : ∀ r ∈ g.roots, |r| ≤ b)
    {x : ℝ} (hx : x ∈ (schurSzegoComp D f g).roots) : |x| ≤ b * v := by
  have hgne : g ≠ 0 := fun h => hg0 (by simp [h])
  have hS : schurSzegoComp D f g ≠ 0 := fun h => by simp [h] at hx
  have hxroot : ((schurSzegoComp D f g).map Complex.ofRealHom).IsRoot (x : ℂ) :=
    Polynomial.IsRoot.map (f := Complex.ofRealHom) ((mem_roots hS).1 hx)
  have := norm_le_mul_of_isRoot_map_schurSzegoComp hv hb hfdeg hgdeg hg0
    (fun w hw => by
      obtain ⟨r, hr, rfl⟩ := exists_eq_ofReal_of_isRoot_map hf0 hfs hw
      simpa using hf r hr)
    (fun w hw => by
      obtain ⟨r, hr, rfl⟩ := exists_eq_ofReal_of_isRoot_map hgne hgs hw
      simpa using hg r hr) (z := (x : ℂ)) hxroot
  simpa using this

/-- The roots of the reflection of a splitting polynomial of exact degree `D` are the inverses
of its roots. -/
private theorem mem_roots_reflect_iff {D : ℕ} {p : ℝ[X]} (hp0 : p ≠ 0) (hps : p.Splits)
    (hdeg : p.natDegree = D) {r : ℝ} (hr : r ∈ (reflect D p).roots) :
    ∃ s ∈ p.roots, s ≠ 0 ∧ r = s⁻¹ := by
  classical
  rw [reflect_eq_X_pow_mul_reverse p hdeg.le, hdeg, Nat.sub_self, pow_zero, one_mul,
    roots_reverse_eq_filter_map_inv hp0 hps] at hr
  obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hr
  rw [Multiset.mem_filter] at hs
  exact ⟨s, hs.1, hs.2, rfl⟩

/-- The constant coefficient of a polynomial rooted away from `0` is nonzero. -/
private theorem coeff_zero_ne_zero_of_isRealRootedIn {S : Set ℝ} {p : ℝ[X]}
    (h : IsRealRootedIn S p) (h0 : (0 : ℝ) ∉ S) : p.coeff 0 ≠ 0 := fun hc =>
  h0 (h.mem_of_isRoot (by simpa [IsRoot.def, coeff_zero_eq_eval_zero] using hc))

/-! ### Reduction to the input degree -/

/-- The degree-`m` factor associated with a degree bound `D`. Its coefficient in degree `k` is
`choose(m, k) / choose(D, k)` times the coefficient of `G`. -/
noncomputable def schurSzegoReduction (D m : ℕ) (G : ℝ[X]) : ℝ[X] :=
  jensenPolynomial m fun k => G.coeff k / (D.choose k : ℝ)

/-- Coefficients of the degree reduction for Schur--Szegő composition. -/
@[simp] theorem coeff_schurSzegoReduction (D m : ℕ) (G : ℝ[X]) (k : ℕ) :
    (schurSzegoReduction D m G).coeff k =
      if k ≤ m then (m.choose k : ℝ) * (G.coeff k / (D.choose k : ℝ)) else 0 := by
  simp [schurSzegoReduction, coeff_jensenPolynomial]

/-- Fixed-right-factor Schur--Szegő composition as a real linear map. -/
@[expose] noncomputable def schurSzegoCompRightLinearMap (D : ℕ) (G : ℝ[X]) :
    ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun f := schurSzegoComp D f G
  map_add' f g := schurSzegoComp_add_left D f g G
  map_smul' c f := by
    simp only [smul_eq_C_mul]
    exact schurSzegoComp_C_mul_left D c f G

/-- Evaluation of fixed-right-factor Schur--Szegő composition. -/
@[simp] theorem schurSzegoCompRightLinearMap_apply (D : ℕ) (G f : ℝ[X]) :
    schurSzegoCompRightLinearMap D G f = schurSzegoComp D f G :=
  rfl

/-- Reducing the second factor from ambient degree `D` to the degree bound `m` does not change
Schur--Szegő composition with an input of degree at most `m`. -/
theorem schurSzegoComp_eq_schurSzegoComp_reduction {D m : ℕ} (hmD : m ≤ D)
    {f G : ℝ[X]} (hf : f.natDegree ≤ m) :
    schurSzegoComp D f G = schurSzegoComp m f (schurSzegoReduction D m G) := by
  ext k
  by_cases hkm : k ≤ m
  · have hkD : k ≤ D := hkm.trans hmD
    have hcm : (m.choose k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℝ) hkm
    have hcD : (D.choose k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℝ) hkD
    rw [coeff_schurSzegoComp_of_le hkD, coeff_schurSzegoComp_of_le hkm,
      coeff_schurSzegoReduction, ite_eq_left hkm]
    field_simp [hcm, hcD]
  · have hmk : m < k := Nat.lt_of_not_ge hkm
    rw [coeff_schurSzegoComp_eq_zero_of_lt hmk]
    by_cases hkD : k ≤ D
    · rw [coeff_schurSzegoComp_of_le hkD,
        coeff_eq_zero_of_natDegree_lt (hf.trans_lt hmk)]
      simp
    · rw [coeff_schurSzegoComp_eq_zero_of_lt (Nat.lt_of_not_ge hkD)]

/-- Arithmetic identity behind the reversal--derivative form of the degree reduction. -/
private theorem factorial_mul_choose_mul_descFactorial {D m k : ℕ} (hmD : m ≤ D)
    (hkm : k ≤ m) :
    m.factorial * (D.choose k * (D - k).descFactorial (D - m)) =
      m.choose k * D.factorial := by
  have hdesc : (m - k).factorial * (D - k).descFactorial (D - m) =
      (D - k).factorial := by
    simpa [show D - k - (D - m) = m - k by lia] using
      Nat.factorial_mul_descFactorial (n := D - k) (k := D - m) (by lia)
  have hchooseD : D.choose k * k.factorial * (D - k).factorial = D.factorial :=
    Nat.choose_mul_factorial_mul_factorial (hkm.trans hmD)
  have hchooseM : m.choose k * k.factorial * (m - k).factorial = m.factorial :=
    Nat.choose_mul_factorial_mul_factorial hkm
  calc
    m.factorial * (D.choose k * (D - k).descFactorial (D - m)) =
        (m.choose k * k.factorial * (m - k).factorial) *
          (D.choose k * (D - k).descFactorial (D - m)) := by rw [hchooseM]
    _ = m.choose k *
        (D.choose k * k.factorial *
          ((m - k).factorial * (D - k).descFactorial (D - m))) := by ring
    _ = m.choose k * (D.choose k * k.factorial * (D - k).factorial) := by
      rw [hdesc]
    _ = m.choose k * D.factorial := by rw [hchooseD]

/-- Ratio form of `factorial_mul_choose_mul_descFactorial`. -/
private theorem choose_div_choose_eq_factorial_div_factorial_mul_descFactorial
    {D m k : ℕ} (hmD : m ≤ D) (hkm : k ≤ m) :
    (m.choose k : ℝ) / (D.choose k : ℝ) =
      (m.factorial : ℝ) / D.factorial * ((D - k).descFactorial (D - m) : ℝ) := by
  have hcD : (D.choose k : ℝ) ≠ 0 :=
    Nat.cast_choose_ne_zero (R := ℝ) (hkm.trans hmD)
  have hfact : (D.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero D
  field_simp [hcD, hfact]
  have h := factorial_mul_choose_mul_descFactorial hmD hkm
  have hreal : (m.choose k : ℝ) * D.factorial =
      m.factorial * (D.choose k * (D - k).descFactorial (D - m)) := by
    exact_mod_cast h.symm
  simpa [mul_assoc, mul_comm, mul_left_comm] using hreal

/-- The degree reduction is a scaled reversal of an iterated derivative of the reversal of `G`.
This is the form used to transport its root interval by Rolle's theorem. -/
theorem schurSzegoReduction_eq_reflect_iterate_derivative {D m : ℕ} (hmD : m ≤ D)
    {G : ℝ[X]} (hGdeg : G.natDegree ≤ D) :
    schurSzegoReduction D m G =
      C ((m.factorial : ℝ) / D.factorial) *
        reflect m ((derivative^[D - m]) (reflect D G)) := by
  ext k
  by_cases hkm : k ≤ m
  · rw [coeff_schurSzegoReduction, ite_eq_left hkm, coeff_C_mul, coeff_reflect,
      revAt_le hkm, coeff_iterate_derivative, coeff_reflect,
      show m - k + (D - m) = D - k by lia, revAt_le (Nat.sub_le D k),
      Nat.sub_sub_self (hkm.trans hmD), nsmul_eq_mul]
    calc
      (m.choose k : ℝ) * (G.coeff k / (D.choose k : ℝ)) =
          ((m.choose k : ℝ) / D.choose k) * G.coeff k := by ring
      _ = ((m.factorial : ℝ) / D.factorial *
          ((D - k).descFactorial (D - m) : ℝ)) * G.coeff k := by
        rw [choose_div_choose_eq_factorial_div_factorial_mul_descFactorial hmD hkm]
      _ = (m.factorial : ℝ) / D.factorial *
          ((D - k).descFactorial (D - m) * G.coeff k) := by ring
  · have hreflectdeg : (reflect D G).natDegree ≤ D :=
      natDegree_reflect_le.trans (by rw [max_eq_left hGdeg])
    have hderdeg : ((derivative^[D - m]) (reflect D G)).natDegree ≤ m :=
      (natDegree_iterate_derivative _ _).trans (by lia)
    have houtdeg :
        (reflect m ((derivative^[D - m]) (reflect D G))).natDegree ≤ m :=
      natDegree_reflect_le.trans (by rw [max_eq_left hderdeg])
    rw [coeff_schurSzegoReduction, ite_eq_right hkm, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (houtdeg.trans_lt (Nat.lt_of_not_ge hkm))]
    simp

/-- Iterated differentiation preserves a closed root interval as long as the derivative is not
taken past the degree. -/
private theorem IsRealRootedIn.iterate_derivative_Icc {p : ℝ[X]} {u v : ℝ}
    (hp : IsRealRootedIn (Icc u v) p) {r : ℕ} (hr : r ≤ p.natDegree) :
    IsRealRootedIn (Icc u v) ((derivative^[r]) p) := by
  induction r generalizing p with
  | zero => simpa using hp
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      have hrp : r ≤ p.natDegree := by lia
      have hq := ih hp hrp
      have hqdeg : (derivative^[r] p).natDegree = p.natDegree - r :=
        natDegree_iterate_derivative_eq_sub hp.ne_zero hrp
      have hqdeg0 : (derivative^[r] p).natDegree ≠ 0 := by lia
      refine ⟨(derivative_ne_zero.mpr hqdeg0), hq.splits.derivative, ?_⟩
      by_cases hqdeg2 : 2 ≤ (derivative^[r] p).natDegree
      · exact roots_derivative_mem_Icc_of_roots_mem_Icc hq.splits hqdeg2
          fun x hx => hq.mem_of_mem_roots hx
      · have hderdeg : (derivative (derivative^[r] p)).natDegree = 0 := by
          rw [(derivative^[r] p).natDegree_derivative]
          lia
        rw [eq_C_of_natDegree_eq_zero hderdeg]
        simp

/-- The reduced factor has the same root interval as the original factor and exact degree `m`.
The interval is bounded away from zero so reversal preserves the degree at both ends. -/
theorem IsRealRootedIn.schurSzegoReduction_Icc {D m : ℕ} {G : ℝ[X]} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hmD : m ≤ D)
    (hG : IsRealRootedIn (Icc (-b) (-a)) G) (hGdeg : G.natDegree = D) :
    IsRealRootedIn (Icc (-b) (-a)) (schurSzegoReduction D m G) ∧
      (schurSzegoReduction D m G).natDegree = m := by
  have hb : 0 < b := ha.trans_le hab
  have hG0 : G.coeff 0 ≠ 0 :=
    coeff_zero_ne_zero_of_isRealRootedIn hG (by
      simp only [mem_Icc]
      intro h
      linarith [h.2])
  let R := reflect D G
  have hR_eq : R = G.reverse := by
    simp only [R, reflect_eq_X_pow_mul_reverse G hGdeg.le, hGdeg, Nat.sub_self, pow_zero,
      one_mul]
  have hRdeg : R.natDegree = D := by
    rw [hR_eq, reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hG0), hGdeg]
    simp
  have hR : IsRealRootedIn (Icc (-a)⁻¹ (-b)⁻¹) R := by
    rw [hR_eq]
    refine hG.reverse_image.mono ?_
    rintro _ ⟨s, hs, rfl⟩
    have hsneg : s < 0 := by linarith [hs.2]
    exact ⟨(inv_le_inv_of_neg (neg_lt_zero.mpr ha) hsneg).2 hs.2,
      (inv_le_inv_of_neg hsneg (neg_lt_zero.mpr hb)).2 hs.1⟩
  let H := (derivative^[D - m]) R
  have hH : IsRealRootedIn (Icc (-a)⁻¹ (-b)⁻¹) H := by
    exact hR.iterate_derivative_Icc (by rw [hRdeg]; lia)
  have hHdeg : H.natDegree = m := by
    dsimp [H]
    rw [natDegree_iterate_derivative_eq_sub hR.ne_zero (by rw [hRdeg]; lia), hRdeg]
    lia
  have hH0 : H.coeff 0 ≠ 0 :=
    coeff_zero_ne_zero_of_isRealRootedIn hH (by
      simp only [mem_Icc]
      have : (-b)⁻¹ < 0 := inv_neg''.2 (neg_lt_zero.mpr hb)
      intro h
      linarith [h.2])
  have hreflect : reflect m H = H.reverse := by
    simp only [reflect_eq_X_pow_mul_reverse H hHdeg.le, hHdeg, Nat.sub_self, pow_zero,
      one_mul]
  have hout : IsRealRootedIn (Icc (-b) (-a)) (reflect m H) := by
    rw [hreflect]
    refine hH.reverse_image.mono ?_
    rintro _ ⟨s, hs, rfl⟩
    have hsneg : s < 0 := hs.2.trans_lt (inv_neg''.2 (neg_lt_zero.mpr hb))
    constructor
    · simpa using
        (inv_le_inv_of_neg (inv_neg''.2 (neg_lt_zero.mpr hb)) hsneg).2 hs.2
    · simpa using
        (inv_le_inv_of_neg hsneg (inv_neg''.2 (neg_lt_zero.mpr ha))).2 hs.1
  have houtdeg : (reflect m H).natDegree = m := by
    rw [hreflect, reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hH0), hHdeg]
    simp
  have hscale : (m.factorial : ℝ) / D.factorial ≠ 0 := by positivity
  rw [schurSzegoReduction_eq_reflect_iterate_derivative hmD hGdeg.le]
  exact ⟨hout.C_mul hscale, by rw [natDegree_C_mul hscale, houtdeg]⟩

/-- Lower root bound: reflecting both factors turns `|root| ≥ a` and `|root| ≥ u` into the upper
bounds `a⁻¹` and `u⁻¹` of `abs_le_mul_of_mem_roots_schurSzegoComp`. -/
theorem le_abs_mul_of_mem_roots_schurSzegoComp {D : ℕ} {f g : ℝ[X]} {u a : ℝ}
    (hu : 0 < u) (ha : 0 < a) (hfs : f.Splits) (hgs : g.Splits)
    (hfdeg : f.natDegree = D) (hgdeg : g.natDegree = D) (hf0 : f.coeff 0 ≠ 0)
    (hg0 : g.coeff 0 ≠ 0) (hf : ∀ r ∈ f.roots, u ≤ |r|) (hg : ∀ r ∈ g.roots, a ≤ |r|)
    {x : ℝ} (hx : x ∈ (schurSzegoComp D f g).roots) : a * u ≤ |x| := by
  have hfne : f ≠ 0 := fun h => hf0 (by simp [h])
  have hgne : g ≠ 0 := fun h => hg0 (by simp [h])
  have hS : schurSzegoComp D f g ≠ 0 := fun h => by simp [h] at hx
  have hxroot : (schurSzegoComp D f g).IsRoot x := (mem_roots hS).1 hx
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_zero_schurSzegoComp] at hxroot
    exact mul_ne_zero hf0 hg0 hxroot
  have hfn : f.coeff D ≠ 0 := hfdeg ▸ leadingCoeff_ne_zero.mpr hfne
  have hgn : g.coeff D ≠ 0 := hgdeg ▸ leadingCoeff_ne_zero.mpr hgne
  have hrf : (reflect D f).natDegree = D :=
    DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne hfdeg.le hf0
  have hrg : (reflect D g).natDegree = D :=
    DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne hgdeg.le hg0
  have hrf0 : reflect D f ≠ 0 := fun h => by simp [h] at hrf; simp_all
  have hrg0 : (reflect D g).coeff 0 ≠ 0 := by
    rw [coeff_reflect, revAt_zero]
    exact hgdeg ▸ hgn
  have hroot : (reflect D (schurSzegoComp D f g)).IsRoot x⁻¹ :=
    (DegreeDropReversal.isRoot_reflect_inv_iff hxne (natDegree_schurSzegoComp_le D f g)).2 hxroot
  rw [reflect_schurSzegoComp] at hroot
  have hS' : schurSzegoComp D (reflect D f) (reflect D g) ≠ 0 := fun h => by
    have hc := congrArg (fun q => q.coeff D) h
    simp only [coeff_schurSzegoComp_of_le le_rfl, Nat.choose_self, Nat.cast_one, div_one,
      coeff_reflect, revAt_le le_rfl, Nat.sub_self, coeff_zero] at hc
    exact mul_ne_zero hf0 hg0 hc
  have key := abs_le_mul_of_mem_roots_schurSzegoComp (inv_nonneg.2 hu.le) (inv_nonneg.2 ha.le)
    hrf0 (hfs.reflect hfdeg.le) (hgs.reflect hgdeg.le) hrf hrg hrg0
    (fun r hr => by
      obtain ⟨s, hs, hs0, rfl⟩ := mem_roots_reflect_iff hfne hfs hfdeg hr
      rw [abs_inv]
      exact inv_anti₀ hu (hf s hs))
    (fun r hr => by
      obtain ⟨s, hs, hs0, rfl⟩ := mem_roots_reflect_iff hgne hgs hgdeg hr
      rw [abs_inv]
      exact inv_anti₀ ha (hg s hs))
    ((mem_roots hS').2 hroot)
  rw [abs_inv, ← mul_inv, inv_le_inv₀ (abs_pos.2 hxne) (by positivity)] at key
  exact key

/-- The composition of two nonzero polynomials of exact degree `D` is nonzero: its coefficient
in degree `D` is the product of the leading coefficients. -/
private theorem schurSzegoComp_ne_zero_of_natDegree_eq {D : ℕ} {f G : ℝ[X]} (hf : f ≠ 0)
    (hG : G ≠ 0) (hfdeg : f.natDegree = D) (hGdeg : G.natDegree = D) :
    schurSzegoComp D f G ≠ 0 := fun h => by
  have hc := congrArg (fun q => q.coeff D) h
  simp only [coeff_schurSzegoComp_of_le le_rfl, Nat.choose_self, Nat.cast_one, div_one,
    coeff_zero] at hc
  exact mul_ne_zero (hfdeg ▸ leadingCoeff_ne_zero.mpr hf)
    (hGdeg ▸ leadingCoeff_ne_zero.mpr hG) hc

/-- **Root intervals of Schur--Szegő compositions** (Kostov--Shapiro, C. R. Acad. Sci. Paris 343
(2006), Theorem 1.1 and Proposition 1.2).  Let `G` have exact degree `D` and roots in
`[-b, -a]`, `0 < a ≤ b`, and let `f` have exact degree `D` and roots in `[-v, -u]`, `0 ≤ u ≤ v`.
Then `schurSzegoComp D f G` is rooted in `[-(b v), -(a u)]`; in particular it is nonzero. -/
theorem IsRealRootedIn.schurSzegoComp_Icc {D : ℕ} {f G : ℝ[X]} {a b u v : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hu : 0 ≤ u) (huv : u ≤ v)
    (hf : IsRealRootedIn (Icc (-v) (-u)) f) (hG : IsRealRootedIn (Icc (-b) (-a)) G)
    (hfdeg : f.natDegree = D) (hGdeg : G.natDegree = D) :
    IsRealRootedIn (Icc (-(b * v)) (-(a * u))) (schurSzegoComp D f G) := by
  have hGneg : ∀ r ∈ G.roots, r < 0 := fun r hr => by
    have := (hG.mem_of_mem_roots hr).2
    linarith
  have hS0 := schurSzegoComp_ne_zero_of_natDegree_eq hf.ne_zero hG.ne_zero hfdeg hGdeg
  have hSs := splits_schurSzegoComp_of_roots_neg hfdeg.le hf.splits hGdeg.le hG.splits hGneg
  have hpos : (schurSzegoComp D f G).roots.countP (0 < ·) = 0 := by
    rw [(schurSzegoComp_roots_sign_counts_of_roots_neg hfdeg hf.splits hGdeg hG.splits hGneg).1,
      Multiset.countP_eq_zero]
    intro r hr
    have := (hf.mem_of_mem_roots hr).2
    simp only [not_lt]
    linarith
  refine ⟨hS0, hSs, fun r hr => ?_⟩
  have hr0 : r ≤ 0 := by
    have := Multiset.countP_eq_zero.1 hpos r hr
    simpa using this
  have hup : |r| ≤ b * v := by
    refine abs_le_mul_of_mem_roots_schurSzegoComp (hu.trans huv) (ha.le.trans hab) hf.ne_zero
      hf.splits hG.splits hfdeg hGdeg
      (coeff_zero_ne_zero_of_isRealRootedIn hG fun h0 => by simp only [mem_Icc] at h0; linarith)
      (fun s hs => ?_) (fun s hs => ?_) hr
    · have := hf.mem_of_mem_roots hs
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    · have := hG.mem_of_mem_roots hs
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
  refine ⟨by linarith [abs_le.1 hup |>.1], ?_⟩
  rcases hu.eq_or_lt with rfl | hu'
  · simpa using hr0
  · have hlow := le_abs_mul_of_mem_roots_schurSzegoComp hu' ha hf.splits hG.splits hfdeg hGdeg
      (coeff_zero_ne_zero_of_isRealRootedIn hf fun h0 => by
        simp only [mem_Icc] at h0; linarith)
      (coeff_zero_ne_zero_of_isRealRootedIn hG fun h0 => by simp only [mem_Icc] at h0; linarith)
      (fun s hs => by
        have := (hf.mem_of_mem_roots hs).2
        rw [abs_of_nonpos (by linarith)]
        linarith)
      (fun s hs => by
        have := (hG.mem_of_mem_roots hs).2
        rw [abs_of_nonpos (by linarith)]
        linarith) hr
    rw [abs_of_nonpos hr0] at hlow
    linarith

/-- **Root intervals of Schur--Szegő compositions for lower-degree inputs.** Let `G` have exact
degree `D` and roots in `[-b, -a]`, with `0 < a ≤ b`, while `f` has degree at most `D` and roots
in `[-v, -u]`, with `0 ≤ u ≤ v`. Then the fixed-degree composition is rooted in
`[-(b * v), -(a * u)]`. -/
theorem IsRealRootedIn.schurSzegoComp_Icc_of_natDegree_le {D : ℕ} {f G : ℝ[X]}
    {a b u v : ℝ} (ha : 0 < a) (hab : a ≤ b) (hu : 0 ≤ u) (huv : u ≤ v)
    (hf : IsRealRootedIn (Icc (-v) (-u)) f) (hG : IsRealRootedIn (Icc (-b) (-a)) G)
    (hfdeg : f.natDegree ≤ D) (hGdeg : G.natDegree = D) :
    IsRealRootedIn (Icc (-(b * v)) (-(a * u))) (schurSzegoComp D f G) := by
  obtain ⟨hGm, hGmdeg⟩ := hG.schurSzegoReduction_Icc ha hab hfdeg hGdeg
  have hrooted := IsRealRootedIn.schurSzegoComp_Icc ha hab hu huv hf hGm rfl hGmdeg
  rwa [← schurSzegoComp_eq_schurSzegoComp_reduction hfdeg le_rfl] at hrooted

/-- A fixed exact-degree factor rooted in `[-b, -a]` maps every input of degree at most `D`
rooted in `[-v, -u]` into `[-(b * v), -(a * u)]`. -/
theorem IsRealRootedIn.maps_schurSzegoComp_Icc {D : ℕ} {G : ℝ[X]} {a b u v : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hu : 0 ≤ u) (huv : u ≤ v)
    (hG : IsRealRootedIn (Icc (-b) (-a)) G) (hGdeg : G.natDegree = D) :
    MapsRealRootedIn (schurSzegoCompRightLinearMap D G) D
      (Icc (-v) (-u)) (Icc (-(b * v)) (-(a * u))) := by
  intro f hfdeg hf
  exact Or.inr (hf.schurSzegoComp_Icc_of_natDegree_le ha hab hu huv hG hfdeg hGdeg)

/-! ### Roots in `[-b v, 0]` -/

/-- The composition with a Taylor shift of the second factor is continuous in the shift: its
complexified evaluations converge as the shift tends to `0`. -/
private theorem tendsto_eval_map_schurSzegoComp_taylor (D : ℕ) (f G : ℝ[X]) (z : ℂ) {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun k => ((schurSzegoComp D f (taylor (e k) G)).map Complex.ofRealHom).eval z) atTop
      (𝓝 (((schurSzegoComp D f G).map Complex.ofRealHom).eval z)) := by
  have hform : ∀ H : ℝ[X], ((schurSzegoComp D f H).map Complex.ofRealHom).eval z =
      ∑ k ∈ Finset.range (D + 1),
        ((f.coeff k * H.coeff k / (D.choose k : ℝ) : ℝ) : ℂ) * z ^ k := fun H => by
    rw [eval_eq_sum_range' (n := D + 1)
      (Nat.lt_succ_of_le (natDegree_map_le.trans (natDegree_schurSzegoComp_le D f H)))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [coeff_map, coeff_schurSzegoComp_of_le (Nat.le_of_lt_succ (Finset.mem_range.1 hk))]
    rfl
  let Ψ : ℝ → ℂ := fun ε => ∑ k ∈ Finset.range (D + 1),
    ((f.coeff k * (hasseDeriv k G).eval ε / (D.choose k : ℝ) : ℝ) : ℂ) * z ^ k
  have hΨ : Continuous Ψ := by
    refine continuous_finsetSum _ fun k _ => ?_
    exact (Complex.continuous_ofReal.comp
      (((continuous_const.mul (Polynomial.continuous _)).div_const _))).mul continuous_const
  have h1 : ∀ ε, ((schurSzegoComp D f (taylor ε G)).map Complex.ofRealHom).eval z = Ψ ε :=
    fun ε => by simp only [hform, taylor_coeff, Ψ]
  have h0 : ((schurSzegoComp D f G).map Complex.ofRealHom).eval z = Ψ 0 := by
    simpa using h1 0
  simp only [h1, h0]
  exact (hΨ.tendsto 0).comp he

/-- **Root intervals of Schur--Szegő compositions, ray version.**  Let `G` have exact degree `D`
and roots in `[-b, 0]`, and let `f` have exact degree `D` and roots in `[-v, 0]`, with
`0 ≤ b` and `0 ≤ v`.  Then `schurSzegoComp D f G` is rooted in `[-(b v), 0]`.

The roots may touch `0`, so `IsRealRootedIn.schurSzegoComp_Icc` does not apply directly.  We apply
it to the Taylor shifts `G(X + ε)`, rooted in `[-(b + ε), -ε]`, and pass to the limit `ε → 0` using
that the roots of a pointwise limit stay in a closed set
(`Polynomial.roots_mem_of_tendsto_eval_of_natDegree_le`).  Taking `b = v = 1` shows that a
full-degree polynomial rooted in `[-1, 0]` preserves the interval `[-1, 0]` under fixed-degree
Schur--Szegő composition with full-degree inputs. -/
theorem IsRealRootedIn.schurSzegoComp_Icc_zero {D : ℕ} {f G : ℝ[X]} {b v : ℝ} (hb : 0 ≤ b)
    (hv : 0 ≤ v) (hf : IsRealRootedIn (Icc (-v) 0) f) (hG : IsRealRootedIn (Icc (-b) 0) G)
    (hfdeg : f.natDegree = D) (hGdeg : G.natDegree = D) :
    IsRealRootedIn (Icc (-(b * v)) 0) (schurSzegoComp D f G) := by
  have hS0 := schurSzegoComp_ne_zero_of_natDegree_eq hf.ne_zero hG.ne_zero hfdeg hGdeg
  have key : ∀ c : ℝ, b * v < c → ∀ z : ℂ,
      ((schurSzegoComp D f G).map Complex.ofRealHom).IsRoot z →
        z.im = 0 ∧ -c ≤ z.re ∧ z.re ≤ 0 := by
    intro c hc z hz
    set δ : ℝ := (c - b * v) / (v + 1) with hδdef
    have hδ : 0 < δ := div_pos (by linarith) (by linarith)
    have hδc : δ * (v + 1) = c - b * v := by rw [hδdef]; field_simp
    set e : ℕ → ℝ := fun k => δ * (1 / ((k : ℝ) + 1)) with hedef
    have he : Tendsto e atTop (𝓝 0) := by
      simpa only [hedef, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
    have hepos : ∀ k, 0 < e k := fun k => by positivity
    have heδ : ∀ k, e k ≤ δ := fun k => by
      have : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      simpa [hedef] using mul_le_mul_of_nonneg_left this hδ.le
    have hrooted : ∀ k, IsRealRootedIn (Icc (-((b + e k) * v)) (-(e k * 0)))
        (schurSzegoComp D f (taylor (e k) G)) := fun k => by
      have hT : IsRealRootedIn (Icc (-(b + e k)) (-(e k))) (taylor (e k) G) := by
        have h := hG.comp_C_mul_X_add_C_Icc_of_pos (e k) one_pos
        rw [taylor_apply, show (X + C (e k) : ℝ[X]) = C 1 * X + C (e k) by simp]
        refine h.mono fun x hx => ?_
        simp only [mem_Icc, div_one] at hx ⊢
        constructor <;> linarith [hx.1, hx.2]
      refine IsRealRootedIn.schurSzegoComp_Icc (hepos k) (by linarith [hepos k]) le_rfl
        (by linarith) (hf.mono fun x hx => ?_) hT hfdeg (by rw [natDegree_taylor, hGdeg])
      simp only [mem_Icc, neg_zero] at hx ⊢
      exact hx
    have hmem := Polynomial.roots_mem_of_tendsto_eval_of_natDegree_le
      (S := {w : ℂ | w.im = 0} ∩ {w : ℂ | -c ≤ w.re} ∩ {w : ℂ | w.re ≤ 0})
      (((isClosed_eq Complex.continuous_im continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_re)).inter
        (isClosed_le Complex.continuous_re continuous_const))
      (p := fun k => (schurSzegoComp D f (taylor (e k) G)).map Complex.ofRealHom)
      (N := D)
      (fun k => natDegree_map_le.trans (natDegree_schurSzegoComp_le D f _))
      (fun k r hr => by
        rw [(hrooted k).splits.roots_map Complex.ofRealHom, Multiset.mem_map] at hr
        obtain ⟨s, hs, rfl⟩ := hr
        have hs' := (hrooted k).mem_of_mem_roots hs
        simp only [mem_Icc] at hs'
        have h1 : (b + e k) * v ≤ c := by
          nlinarith [heδ k, mul_le_mul_of_nonneg_right (heδ k) hv]
        refine ⟨⟨Complex.ofReal_im s, ?_⟩, ?_⟩
        · change -c ≤ (s : ℂ).re
          rw [Complex.ofReal_re]
          linarith [hs'.1]
        · change (s : ℂ).re ≤ 0
          rw [Complex.ofReal_re]
          simpa using hs'.2)
      (fun μ => tendsto_eval_map_schurSzegoComp_taylor D f G μ he)
      z ((mem_roots (Polynomial.map_ne_zero hS0)).2 hz)
    exact ⟨hmem.1.1, hmem.1.2, hmem.2⟩
  have hroot : ∀ x ∈ (schurSzegoComp D f G).roots,
      ((schurSzegoComp D f G).map Complex.ofRealHom).IsRoot (x : ℂ) := fun x hx =>
    Polynomial.IsRoot.map (f := Complex.ofRealHom) ((mem_roots hS0).1 hx)
  refine ⟨hS0, Polynomial.splits_of_all_roots_real fun z hz => (key _ (lt_add_one _) z hz).1,
    fun x hx => ⟨?_, ?_⟩⟩
  · by_contra hlt
    push Not at hlt
    have := (key ((b * v - x) / 2) (by linarith) (x : ℂ) (hroot x hx)).2.1
    simp only [Complex.ofReal_re] at this
    linarith
  · simpa using (key (b * v + 1) (lt_add_one _) (x : ℂ) (hroot x hx)).2.2

/-- **Ray root intervals for lower-degree inputs.** Let `G` have exact degree `D` and roots in
`[-b, 0]`, and let `f` have degree at most `D` and roots in `[-v, 0]`. The composition is either
zero or rooted in `[-(b * v), 0]`. Zero output can occur because roots of `G` at zero may erase
all coefficients visible to `f`. -/
theorem IsRealRootedIn.schurSzegoComp_Icc_zero_of_natDegree_le {D : ℕ} {f G : ℝ[X]}
    {b v : ℝ} (hb : 0 ≤ b) (hv : 0 ≤ v) (hf : IsRealRootedIn (Icc (-v) 0) f)
    (hG : IsRealRootedIn (Icc (-b) 0) G) (hfdeg : f.natDegree ≤ D)
    (hGdeg : G.natDegree = D) :
    schurSzegoComp D f G = 0 ∨
      IsRealRootedIn (Icc (-(b * v)) 0) (schurSzegoComp D f G) := by
  by_cases hS0 : schurSzegoComp D f G = 0
  · exact Or.inl hS0
  refine Or.inr ?_
  have key : ∀ c : ℝ, b * v < c → ∀ z : ℂ,
      ((schurSzegoComp D f G).map Complex.ofRealHom).IsRoot z →
        z.im = 0 ∧ -c ≤ z.re ∧ z.re ≤ 0 := by
    intro c hc z hz
    set δ : ℝ := (c - b * v) / (v + 1) with hδdef
    have hδ : 0 < δ := div_pos (by linarith) (by linarith)
    have hδc : δ * (v + 1) = c - b * v := by rw [hδdef]; field_simp
    set e : ℕ → ℝ := fun k => δ * (1 / ((k : ℝ) + 1)) with hedef
    have he : Tendsto e atTop (𝓝 0) := by
      simpa only [hedef, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
    have hepos : ∀ k, 0 < e k := fun k => by positivity
    have heδ : ∀ k, e k ≤ δ := fun k => by
      have : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      simpa [hedef] using mul_le_mul_of_nonneg_left this hδ.le
    have hrooted : ∀ k, IsRealRootedIn (Icc (-((b + e k) * v)) (-(e k * 0)))
        (schurSzegoComp D f (taylor (e k) G)) := fun k => by
      have hT : IsRealRootedIn (Icc (-(b + e k)) (-(e k))) (taylor (e k) G) := by
        have h := hG.comp_C_mul_X_add_C_Icc_of_pos (e k) one_pos
        rw [taylor_apply, show (X + C (e k) : ℝ[X]) = C 1 * X + C (e k) by simp]
        refine h.mono fun x hx => ?_
        simp only [mem_Icc, div_one] at hx ⊢
        constructor <;> linarith [hx.1, hx.2]
      refine IsRealRootedIn.schurSzegoComp_Icc_of_natDegree_le (hepos k)
        (by linarith [hepos k]) le_rfl (by linarith) (hf.mono fun x hx => ?_) hT hfdeg
        (by rw [natDegree_taylor, hGdeg])
      simp only [mem_Icc, neg_zero] at hx ⊢
      exact hx
    have hmem := Polynomial.roots_mem_of_tendsto_eval_of_natDegree_le
      (S := {w : ℂ | w.im = 0} ∩ {w : ℂ | -c ≤ w.re} ∩ {w : ℂ | w.re ≤ 0})
      (((isClosed_eq Complex.continuous_im continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_re)).inter
        (isClosed_le Complex.continuous_re continuous_const))
      (p := fun k => (schurSzegoComp D f (taylor (e k) G)).map Complex.ofRealHom)
      (N := D)
      (fun k => natDegree_map_le.trans (natDegree_schurSzegoComp_le D f _))
      (fun k r hr => by
        rw [(hrooted k).splits.roots_map Complex.ofRealHom, Multiset.mem_map] at hr
        obtain ⟨s, hs, rfl⟩ := hr
        have hs' := (hrooted k).mem_of_mem_roots hs
        simp only [mem_Icc] at hs'
        have h1 : (b + e k) * v ≤ c := by
          nlinarith [heδ k, mul_le_mul_of_nonneg_right (heδ k) hv]
        refine ⟨⟨Complex.ofReal_im s, ?_⟩, ?_⟩
        · change -c ≤ (s : ℂ).re
          rw [Complex.ofReal_re]
          linarith [hs'.1]
        · change (s : ℂ).re ≤ 0
          rw [Complex.ofReal_re]
          simpa using hs'.2)
      (fun μ => tendsto_eval_map_schurSzegoComp_taylor D f G μ he)
      z ((mem_roots (Polynomial.map_ne_zero hS0)).2 hz)
    exact ⟨hmem.1.1, hmem.1.2, hmem.2⟩
  have hsplits := Polynomial.splits_of_all_roots_real fun z hz =>
    (key _ (lt_add_one _) z hz).1
  refine ⟨hS0, hsplits, fun x hx => ?_⟩
  have hxroot : ((schurSzegoComp D f G).map Complex.ofRealHom).IsRoot (x : ℂ) :=
    Polynomial.IsRoot.map (f := Complex.ofRealHom) ((mem_roots hS0).1 hx)
  constructor
  · by_contra hlt
    push Not at hlt
    have := (key ((b * v - x) / 2) (by linarith) (x : ℂ) hxroot).2.1
    simp only [Complex.ofReal_re] at this
    linarith
  · simpa using (key (b * v + 1) (lt_add_one _) (x : ℂ) hxroot).2.2

/-- A fixed exact-degree factor rooted in `[-b, 0]` maps inputs rooted in `[-v, 0]` into
`[-(b * v), 0]`, with the zero output permitted by `MapsRealRootedIn`. -/
theorem IsRealRootedIn.maps_schurSzegoComp_Icc_zero {D : ℕ} {G : ℝ[X]} {b v : ℝ}
    (hb : 0 ≤ b) (hv : 0 ≤ v) (hG : IsRealRootedIn (Icc (-b) 0) G)
    (hGdeg : G.natDegree = D) :
    MapsRealRootedIn (schurSzegoCompRightLinearMap D G) D
      (Icc (-v) 0) (Icc (-(b * v)) 0) := by
  intro f hfdeg hf
  exact hf.schurSzegoComp_Icc_zero_of_natDegree_le hb hv hG hfdeg hGdeg

end RealRooted
