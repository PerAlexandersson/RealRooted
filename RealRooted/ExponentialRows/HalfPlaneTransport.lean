module

public import RealRooted.HermiteBiehler.Basic
import RealRooted.HermiteBiehler.Converse
import RealRooted.HermiteBiehler.Converse.Wronskian
import RealRooted.HermiteBiehler.Forward
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic

/-!
# Transport of strict half-plane root location

In a continuous fixed-degree family the parameters with a root in the closed
upper half-plane form a closed set. Cauchy's bound lets us project the root
equation from the compact unit disk, even for an unbounded parameter space.
The complementary closure theorem transports Hermite–Biehler stability across
a connected parameter space when real-axis crossings are excluded.

Source: the deformation argument in RealRooted issue #2649,
https://github.com/PerAlexandersson/RealRooted/issues/2649.
-/

public section

open Polynomial Filter Topology Set

namespace RealRooted

/-- Joint evaluation is continuous for a coefficient-continuous, bounded-degree family. -/
private theorem continuous_family_eval {B : Type*} [TopologicalSpace B]
    {F : B → ℂ[X]} {d : ℕ} (hf : ∀ i, Continuous fun x => (F x).coeff i)
    (hd : ∀ x, (F x).natDegree ≤ d) :
    Continuous fun u : B × ℂ => (F u.1).eval u.2 := by
  simp_rw [eval_eq_sum_range' (Nat.lt_succ_of_le (hd _))]
  exact continuous_finsetSum _ fun i _ => ((hf i).comp continuous_fst).mul (continuous_snd.pow i)

/-- Fixed degree and continuous coefficients make strict lower-half-plane
root location an open condition. -/
theorem isOpen_roots_im_neg {B : Type*} [TopologicalSpace B]
    {F : B → ℂ[X]} {d : ℕ} (hf : ∀ i, Continuous fun x => (F x).coeff i)
    (hne : ∀ x, F x ≠ 0) (hd : ∀ x, (F x).natDegree = d) :
    IsOpen {x | ∀ z : ℂ, (F x).IsRoot z → z.im < 0} := by
  classical
  let M (x : B) : ℝ := (F x).cauchyBound
  have hM : Continuous M := by
    apply NNReal.continuous_coe.comp
    simp only [cauchyBound, leadingCoeff, hd]
    exact ((Continuous.finset_sup_apply (fun i _ => (hf i).nnNorm)).div₀ (hf d).nnNorm
      (fun x => by simpa only [← hd x, coeff_natDegree, ne_eq, nnNorm_eq_zero] using
        leadingCoeff_ne_zero.mpr (hne x))).add continuous_const
  have hpos (x : B) : 0 < M x := by
    exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast one_le_cauchyBound (F x))
  let K := Metric.closedBall (0 : ℂ) 1
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let Z (u : B × K) : ℂ := (M u.1 : ℂ) * (u.2 : ℂ)
  have hZ : Continuous Z := ((Complex.continuous_ofReal.comp hM).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)
  let S : Set (B × K) := {u | (F u.1).eval (Z u) = 0 ∧ 0 ≤ (Z u).im}
  have hs : IsClosed S :=
    (isClosed_eq ((continuous_family_eval hf (fun x => (hd x).le)).comp
      (continuous_fst.prodMk hZ)) continuous_const).inter
      (isClosed_le continuous_const (Complex.continuous_im.comp hZ))
  have he : {x | ∀ z : ℂ, (F x).IsRoot z → z.im < 0} = (Prod.fst '' S)ᶜ := by
    ext x
    change (∀ z : ℂ, (F x).IsRoot z → z.im < 0) ↔ x ∉ Prod.fst '' S
    constructor
    · rintro hx ⟨⟨y, w⟩, hw, rfl⟩
      exact (hx _ hw.1).not_ge hw.2
    · intro hx z hz
      by_contra! him
      have hM0 := (hpos x).ne'
      have hw : z / (M x : ℂ) ∈ K := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_div, Complex.norm_real,
          Real.norm_of_nonneg (hpos x).le, div_le_iff₀ (hpos x), one_mul]
        exact_mod_cast (hz.norm_lt_cauchyBound (hne x)).le
      let w : K := ⟨_, hw⟩
      have he : Z (x, w) = z := by
        change (M x : ℂ) * (z / (M x : ℂ)) = z
        rw [← mul_div_assoc]
        exact mul_div_cancel_left₀ z (Complex.ofReal_ne_zero.mpr hM0)
      apply hx
      refine ⟨(x, w), ?_, rfl⟩
      change (F x).eval (Z (x, w)) = 0 ∧ 0 ≤ (Z (x, w)).im
      exact he.symm ▸ And.intro hz.eq_zero him
  rw [he]
  exact (isClosedMap_fst_of_compactSpace S hs).isOpen_compl

/-- Along a connected fixed-degree deformation, absence of real roots transports
upper-half-plane stability from any one parameter. -/
theorem isUpperHalfPlaneStable_of_no_real_root {B : Type*} [PseudoMetricSpace B]
    [PreconnectedSpace B] {F : B → ℂ[X]} {d : ℕ}
    (hf : ∀ i, Continuous fun x => (F x).coeff i)
    (hne : ∀ x, F x ≠ 0) (hd : ∀ x, (F x).natDegree = d)
    (hreal : ∀ x (r : ℝ), (F x).eval (r : ℂ) ≠ 0)
    {x₀ : B} (h₀ : IsUpperHalfPlaneStable (F x₀)) (x : B) :
    IsUpperHalfPlaneStable (F x) := by
  let S : Set B := {y | ∀ z : ℂ, (F y).IsRoot z → z.im < 0}
  have hiff (y : B) : y ∈ S ↔ IsUpperHalfPlaneStable (F y) := by
    constructor
    · intro h z hz he
      exact hz.not_ge (h z he).le
    · intro h z hz
      rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
      · exact hneg
      · have he : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using hzero.symm)
        exact ((hreal y z.re) (by rw [he]; exact hz)).elim
      · exact (h z hpos hz).elim
  have hc : IsClosed S := by
    apply IsSeqClosed.isClosed
    intro u y hu hy
    apply (hiff y).2
    intro z hz he
    have hloc := roots_mem_of_tendsto_eval_of_natDegree_le
      (S := {v : ℂ | v.im ≤ 0}) (isClosed_le Complex.continuous_im continuous_const)
      (fun k => (hd (u k)).le) (fun k v hv => (hu k v (isRoot_of_mem_roots hv)).le)
      (p₀ := F y) (fun v => ((continuous_family_eval hf (fun j => (hd j).le)).tendsto
        (y, v)).comp (hy.prodMk_nhds tendsto_const_nhds))
    exact hz.not_ge (hloc z ((mem_roots (hne y)).mpr he))
  have hU := (show IsClopen S from ⟨hc, isOpen_roots_im_neg hf hne hd⟩).eq_univ
    ⟨x₀, (hiff x₀).2 h₀⟩
  apply (hiff x).1
  simp [hU]

/-- The real part of the top Hermite–Biehler coefficient prevents cancellation. -/
private theorem natDegree_hb_of_le {f g : ℝ[X]} (hf : f ≠ 0) (hg : g.natDegree ≤ f.natDegree) :
    (hermiteBiehlerPolynomial f g).natDegree = f.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_add_le _ _).trans (max_le (natDegree_map_le.trans le_rfl)
      ((natDegree_C_mul_le ..).trans (natDegree_map_le.trans hg)))
  · intro he
    have hr := congrArg Complex.re he
    simp only [hermiteBiehlerPolynomial, complexify, AddMonoidAlgebra.coeff_add,
      Finsupp.coe_add, Pi.add_apply, coeff_map, coeff_natDegree, Complex.ofRealHom_eq_coe,
      coeff_C_mul, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.zero_re,
      leadingCoeff_eq_zero] at hr
    exact hf hr

/-- Oriented root interleaving propagates along any connected fixed-degree family of
disjoint pairs with positive leading coefficients. The proof tracks the half-plane
of the Hermite–Biehler roots and allows collisions within either individual row. -/
theorem strictInterl_of_no_common_root_family {B : Type*} [PseudoMetricSpace B]
    [PreconnectedSpace B] {f g : B → ℝ[X]} {d : ℕ} (hd : d ≠ 0)
    (hf : ∀ i, Continuous fun x => (f x).coeff i) (hg : ∀ i, Continuous fun x => (g x).coeff i)
    (hfpos : ∀ x, HasPosLeadingCoeff (f x)) (hgpos : ∀ x, HasPosLeadingCoeff (g x))
    (hdeg : ∀ x, (f x).natDegree = d) (hle : ∀ x, (g x).natDegree ≤ d)
    (hdis : ∀ x r, ¬ ((g x).IsRoot r ∧ (f x).IsRoot r))
    {x₀ : B} (h₀ : StrictInterl (g x₀) (f x₀)) (x : B) :
    StrictInterl (g x) (f x) := by
  let H (y : B) := hermiteBiehlerPolynomial (f y) (g y)
  have hr (y : B) := hnoreal_of_no_common_real_root (f := f y) (g := g y)
    (fun ⟨r, hu, hv⟩ => hdis y r ⟨hv, hu⟩)
  have hco (i : ℕ) : Continuous fun y => (H y).coeff i := by
    simp only [H, hermiteBiehlerPolynomial, complexify, coeff_add, coeff_C_mul, coeff_map,
      Complex.ofRealHom_eq_coe]
    exact (Complex.continuous_ofReal.comp (hf i)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp (hg i)))
  apply strictInterl_of_stable_general (hfpos x) (hgpos x) _ (by rw [hdeg]; lia)
  exact isUpperHalfPlaneStable_of_no_real_root (F := H) hco
    (fun y he => hr y 0 (by change (H y).eval _ = _; simp [he]))
    (fun y => (natDegree_hb_of_le (hfpos y).ne_zero ((hdeg y).symm ▸ hle y)).trans (hdeg y))
    hr (hermiteBiehlerForwardPos (hfpos x₀) (hgpos x₀) h₀) x

end RealRooted
