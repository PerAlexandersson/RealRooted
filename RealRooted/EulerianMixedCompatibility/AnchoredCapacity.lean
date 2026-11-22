module

public import RealRooted.EulerianMixedCompatibility.Insertion
import RealRooted.AffineDerivative
import RealRooted.PosCombo
import RealRooted.CommonInterleaver.SuccDegreeLowDegree
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.WagnerX.AffineFactors
import RealRooted.MaWang.Weak.DerivativeSign
import RealRooted.SimpleRoots

/-!
# Anchored Euler capacity transport

We formalize §§1–4 of the unpublished manuscript
`weyl-operators/notes/anchored-euler-capacity-matrices.md` (RealRooted #1878).
An anchored state `(p,1)` transports an interval of split constant shifts. This is an
actual-state certificate; it supplies neither universal matrix preservation nor an adjacent edge.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Every constant shift with level in the closed interval splits. -/
@[expose] def LevelCapacity (a b : ℝ) (p : ℝ[X]) : Prop :=
  ∀ s, a ≤ s → s ≤ b → (p - C s).Splits

/-- Capacity can be restricted to a smaller interval. -/
theorem LevelCapacity.mono {a b a' b' : ℝ} {p : ℝ[X]} (h : LevelCapacity a b p)
    (ha : a ≤ a') (hb : b' ≤ b) : LevelCapacity a' b' p := by
  intro s hs ht
  exact h s (ha.trans hs) (ht.trans hb)

/-- The division-free affine identity transporting a level through an anchored Euler step. -/
theorem eulerInsertionStep_add_const_sub_const (c lambda s : ℝ) (d : ℕ) (p : ℝ[X]) :
    eulerInsertionStep c d p + C lambda - C (lambda + c * s) =
      eulerInsertionStep 0 d p + C c * (p - C s) := by
  simp only [eulerInsertionStep, map_zero, zero_mul, zero_add, map_add, map_mul]
  ring

/-- Inverse affine form of the exact shift identity. Only the algebraic nonzero gate
is needed here; positivity is reserved for interval membership and compatibility. -/
theorem eulerInsertionStep_add_const_sub_const_div {c : ℝ} (hc : c ≠ 0)
    (lambda t : ℝ) (d : ℕ) (p : ℝ[X]) :
    eulerInsertionStep c d p + C lambda - C t =
      eulerInsertionStep 0 d p + C c * (p - C ((t - lambda) / c)) := by
  have h := eulerInsertionStep_add_const_sub_const c lambda ((t - lambda) / c) d p
  have heq : lambda + c * ((t - lambda) / c) = t := by field_simp [hc]; ring
  rwa [heq] at h

/-- Positive boundary weight transports compatible shifts, with nonzeroness explicit. -/
theorem levelCapacity_eulerInsertionStep_add_const
    {c a b lambda : ℝ} {d : ℕ} {p : ℝ[X]} (hc : 0 < c)
    (hcompat : ∀ s, a ≤ s → s ≤ b → Compatible (eulerInsertionStep 0 d p) (p - C s))
    (hne : ∀ t, lambda + c * a ≤ t → t ≤ lambda + c * b →
      eulerInsertionStep c d p + C lambda - C t ≠ 0) :
    LevelCapacity (lambda + c * a) (lambda + c * b)
      (eulerInsertionStep c d p + C lambda) := by
  intro t ht hu
  have ha : a ≤ (t - lambda) / c := (le_div_iff₀ hc).2 (by linarith)
  have hb : (t - lambda) / c ≤ b := (div_le_iff₀ hc).2 (by linarith)
  have hid := eulerInsertionStep_add_const_sub_const_div hc.ne' lambda t d p
  rw [hid]
  exact (hcompat _ ha hb).splits_add_C_mul hc.le (hid ▸ hne t ht hu)

/-- Degree growth excludes the zero alternative in compatibility transport.
In particular, this supplies the nonzero gate for PF inputs. -/
theorem levelCapacity_eulerInsertionStep_add_const_of_degree
    {c a b lambda : ℝ} {d : ℕ} {p : ℝ[X]} (hc : 0 < c)
    (hp : HasPosLeadingCoeff p) (hd : p.natDegree ≤ d)
    (hcompat : ∀ s, a ≤ s → s ≤ b → Compatible (eulerInsertionStep 0 d p) (p - C s)) :
    LevelCapacity (lambda + c * a) (lambda + c * b)
      (eulerInsertionStep c d p + C lambda) := by
  apply levelCapacity_eulerInsertionStep_add_const hc hcompat
  intro t _ _ hz
  have hdeg := (eulerInsertionStep_degree_pos (c := c) hd hp).1
  have heq := congrArg natDegree hz
  simp only [natDegree_sub_C, natDegree_add_C, natDegree_zero] at heq
  lia

/-- Zero boundary weight has a singleton target interval and needs no division. -/
theorem levelCapacity_eulerInsertionStep_zero_add_const
    {lambda : ℝ} {d : ℕ} {p : ℝ[X]} (h : (eulerInsertionStep 0 d p).Splits) :
    LevelCapacity lambda lambda (eulerInsertionStep 0 d p + C lambda) := by
  intro t ht hu
  have : t = lambda := le_antisymm hu ht
  simpa [this] using h

/-- Positive leading coefficient is unchanged by subtracting a constant at positive degree. -/
private lemma posLeading_sub_const {p : ℝ[X]} (hp : HasPosLeadingCoeff p)
    (hd : p.natDegree ≠ 0) (s : ℝ) : HasPosLeadingCoeff (p - C s) := by
  change 0 < (p - C s).leadingCoeff
  rw [leadingCoeff, natDegree_sub_C, coeff_sub, coeff_C, ite_eq_right hd, sub_zero]
  exact hp

/-- Constant shifts interpolate exactly between two distinct levels. -/
theorem sub_const_eq_endpoint_combo {a b : ℝ} (hab : a < b) (s : ℝ) (p : ℝ[X]) :
    p - C s = C ((b - s) / (b - a)) * (p - C a) +
      C ((s - a) / (b - a)) * (p - C b) := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hw : (b - s) / (b - a) + (s - a) / (b - a) = 1 := by field_simp [hne]; ring
  have hl : (b - s) / (b - a) * a + (s - a) / (b - a) * b = s := by
    field_simp [hne]
    ring
  calc
    p - C s = C (1 : ℝ) * p - C s := by simp
    _ = C ((b - s) / (b - a) + (s - a) / (b - a)) * p -
        C ((b - s) / (b - a) * a + (s - a) / (b - a) * b) := by rw [hw, hl]
    _ = _ := by simp only [map_add, map_mul]; ring

/-- Two endpoint edges control every shift between them. Endpoints and singleton intervals
are handled without applying strict interlacing to a zero scalar multiple. -/
theorem strictInterl_sub_const_of_endpoints {p m : ℝ[X]} {a b s : ℝ}
    (hp : HasPosLeadingCoeff p) (hd : p.natDegree ≠ 0) (hm : HasPosLeadingCoeff m)
    (ha : StrictInterl m (p - C a)) (hb : StrictInterl m (p - C b))
    (hs : a ≤ s) (ht : s ≤ b) : StrictInterl m (p - C s) := by
  by_cases hsa : s = a
  · simpa [hsa] using ha
  by_cases hsb : s = b
  · simpa [hsb] using hb
  have has : a < s := lt_of_le_of_ne hs (Ne.symm hsa)
  have hsb' : s < b := lt_of_le_of_ne ht hsb
  have hab : a < b := has.trans hsb'
  have hw : 0 < (b - s) / (b - a) := div_pos (sub_pos.mpr hsb') (sub_pos.mpr hab)
  have hv : 0 < (s - a) / (b - a) := div_pos (sub_pos.mpr has) (sub_pos.mpr hab)
  rw [sub_const_eq_endpoint_combo hab s p]
  have hsum := StrictInterl.sum_left_of_common_left
    [C ((b - s) / (b - a)) * (p - C a), C ((s - a) / (b - a)) * (p - C b)] m
    (by simp only [List.mem_cons, List.not_mem_nil, or_false];
        rintro q (rfl | rfl)
        · exact ha.C_mul_right hw.ne'
        · exact hb.C_mul_right hv.ne') hm
    (by simp only [List.mem_cons, List.not_mem_nil, or_false];
        rintro q (rfl | rfl)
        · exact hasPosLeadingCoeff_C_mul hw (posLeading_sub_const hp hd a)
        · exact hasPosLeadingCoeff_C_mul hv (posLeading_sub_const hp hd b)) (by simp)
  simpa using hsum

/-- The zero-boundary Euler step is `X` times the affine derivative companion. -/
theorem eulerInsertionStep_zero_eq_X_mul (d : ℕ) (p : ℝ[X]) :
    eulerInsertionStep 0 d p = X * (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative) := by
  simp only [eulerInsertionStep, map_zero, zero_mul, zero_add]
  ring

/-- A single affine-derivative edge supplies splitness at the corresponding target level.
Degree growth excludes the zero combination. This is the pointwise capacity frontend. -/
theorem splits_eulerInsertionStep_add_const_sub_const
    {p : ℝ[X]} {d : ℕ} {c lambda t : ℝ} (hc : 0 < c)
    (hp : HasPosLeadingCoeff p) (hd : p.natDegree ≤ d)
    (he : StrictInterl (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative)
      (p - C ((t - lambda) / c)))
    (hmnn : HasNonnegCoeffs (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative))
    (hnn : HasNonnegCoeffs (p - C ((t - lambda) / c))) :
    (eulerInsertionStep c d p + C lambda - C t).Splits := by
  have hcompat : Compatible (eulerInsertionStep 0 d p) (p - C ((t - lambda) / c)) := by
    rw [eulerInsertionStep_zero_eq_X_mul]
    exact (Compatible.of_strictInterl
      (strictInterl_mul_X_of_strictInterl_of_nonneg he hmnn hnn)).comm
  have hid := eulerInsertionStep_add_const_sub_const_div hc.ne' lambda t d p
  rw [hid]
  apply hcompat.splits_add_C_mul hc.le
  rw [← hid]
  intro hz
  have hdeg := (eulerInsertionStep_degree_pos (c := c) hd hp).1
  have heq := congrArg natDegree hz
  simp only [natDegree_sub_C, natDegree_add_C, natDegree_zero] at heq
  lia

/-- Endpoint interpolation and positive-`X` transfer supply all required compatibilities. -/
theorem compatible_eulerInsertionStep_zero_sub_const_of_endpoints
    {p : ℝ[X]} {d : ℕ} {a b s : ℝ}
    (hp : HasPosLeadingCoeff p) (hd : p.natDegree ≠ 0)
    (hm : HasPosLeadingCoeff (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative))
    (hmnn : HasNonnegCoeffs (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative))
    (ha : StrictInterl (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative) (p - C a))
    (hb : StrictInterl (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative) (p - C b))
    (hnn : HasNonnegCoeffs (p - C s)) (hs : a ≤ s) (ht : s ≤ b) :
    Compatible (eulerInsertionStep 0 d p) (p - C s) := by
  rw [eulerInsertionStep_zero_eq_X_mul]
  exact (Compatible.of_strictInterl (strictInterl_mul_X_of_strictInterl_of_nonneg
    (strictInterl_sub_const_of_endpoints hp hd hm ha hb hs ht) hmnn hnn)).comm

/-- Two endpoint edges give affine capacity transport, with degree-based nonzeroness. -/
theorem levelCapacity_eulerInsertionStep_add_const_of_endpoints
    {p : ℝ[X]} {d : ℕ} {c a b lambda : ℝ} (hc : 0 < c)
    (hp : HasPosLeadingCoeff p) (hd : p.natDegree ≠ 0) (hbound : p.natDegree ≤ d)
    (hm : HasPosLeadingCoeff (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative))
    (hmnn : HasNonnegCoeffs (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative))
    (ha : StrictInterl (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative) (p - C a))
    (hb : StrictInterl (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative) (p - C b))
    (hnn : ∀ s, a ≤ s → s ≤ b → HasNonnegCoeffs (p - C s)) :
    LevelCapacity (lambda + c * a) (lambda + c * b)
      (eulerInsertionStep c d p + C lambda) := by
  apply levelCapacity_eulerInsertionStep_add_const_of_degree hc hp hbound
  intro s hs ht
  exact compatible_eulerInsertionStep_zero_sub_const_of_endpoints hp hd hm hmnn ha hb
    (hnn s hs ht) hs ht

/-- On `[0,b]`, the affine-derivative theorem discharges the left endpoint.
The only orbit-specific interlacing premise is the edge at `b`. -/
theorem levelCapacity_eulerInsertionStep_add_const_of_endpoint
    {p : ℝ[X]} {d : ℕ} {c b lambda : ℝ} (hc : 0 < c)
    (hp : p.Splits) (hd : p.natDegree ≠ 0) (hbound : p.natDegree ≤ d)
    (hpnn : HasNonnegCoeffs p)
    (hm : HasPosLeadingCoeff (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative))
    (hmnn : HasNonnegCoeffs (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative))
    (hb : StrictInterl (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative) (p - C b))
    (hnn : ∀ s, 0 ≤ s → s ≤ b → HasNonnegCoeffs (p - C s)) :
    LevelCapacity lambda (lambda + c * b) (eulerInsertionStep c d p + C lambda) := by
  have hpne : p ≠ 0 := by intro hz; simp [hz] at hd
  have ha := strictInterl_affine_derivative_of_nonnegCoeffs hp (by lia) hpnn
    (c := (d : ℝ) + 1) (by exact_mod_cast Nat.lt_succ_of_le hbound)
  simpa using levelCapacity_eulerInsertionStep_add_const_of_endpoints hc
    (hpnn.pos_leadingCoeff hpne) hd hbound hm hmnn (by simpa using ha) hb hnn

/-- A same-degree polynomial with positive derivative-oriented signs at all roots precedes
that simple split row. We reuse the successor sign theorem by adding a far-right root. -/
private theorem strictInterl_of_eval_mul_derivative_pos_same
    {h m : ℝ[X]} (hh : HasPosLeadingCoeff h) (hs : h.Splits) (hn : h.roots.Nodup)
    (hm : HasPosLeadingCoeff m) (hd : m.natDegree = h.natDegree)
    (hflux : ∀ r, h.IsRoot r → 0 < m.eval r * h.derivative.eval r) :
    StrictInterl m h := by
  obtain ⟨bm, hbm⟩ := exists_root_upper_bound m
  obtain ⟨bh, hbh⟩ := exists_root_upper_bound h
  let R := max bm bh + 1
  have hmR : ∀ r ∈ m.roots, r ≤ R := by
    intro r hr
    exact (hbm r hr).trans (by dsimp [R]; linarith [le_max_left bm bh])
  have hhR : ∀ r ∈ h.roots, r ≤ R := by
    intro r hr
    exact (hbh r hr).trans (by dsimp [R]; linarith [le_max_right bm bh])
  have he : StrictInterl h ((X - C R) * m) := by
    apply strictInterl_of_eval_mul_derivative_nonpos hh hs hn
      (hasPosLeadingCoeff_X_sub_C_mul hm)
    · rw [natDegree_mul (X_sub_C_ne_zero R) hm.ne_zero, natDegree_X_sub_C, hd]
      lia
    · rw [natDegree_mul (X_sub_C_ne_zero R) hm.ne_zero, natDegree_X_sub_C, hd]
      lia
    · intro r hr
      have hrR : r - R ≤ 0 := sub_nonpos.mpr (hhR r ((mem_roots hh.ne_zero).2 hr))
      simp only [eval_mul, eval_sub, eval_X, eval_C]
      rw [mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg hrR (hflux r hr).le
  exact he.of_mul_X_sub_C_of_sameDegree_of_roots_le hd hm hh hmR hhR

/-- Descending-root flux is the only nonautomatic endpoint sign.
Simple nonpositive roots and all degree/leading gates remain explicit. -/
theorem strictInterl_affineDerivative_sub_const_of_rootFlux
    {p : ℝ[X]} {d : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hh : HasPosLeadingCoeff (p - C b)) (hs : (p - C b).Splits)
    (hn : (p - C b).roots.Nodup)
    (hm : HasPosLeadingCoeff (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative))
    (hd : (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative).natDegree =
      (p - C b).natDegree)
    (hroots : ∀ r, (p - C b).IsRoot r → r ≤ 0)
    (hflux : ∀ r, (p - C b).IsRoot r → p.derivative.eval r < 0 →
      ((d : ℝ) + 1) * b < (1 - r) * (-p.derivative.eval r)) :
    StrictInterl (C ((d : ℝ) + 1) * p + (1 - X) * p.derivative) (p - C b) := by
  apply strictInterl_of_eval_mul_derivative_pos_same hh hs hn hm hd
  intro r hr
  have hpval : p.eval r = b := sub_eq_zero.mp (by simpa [IsRoot.def] using hr)
  have hder : p.derivative.eval r ≠ 0 := by
    simpa using (HasSimpleRoots.of_roots_nodup hh.ne_zero hn).eval_derivative_ne_zero hr
  have hone : 0 < 1 - r := by linarith [hroots r hr]
  have hmass : 0 ≤ ((d : ℝ) + 1) * b := mul_nonneg (by positivity) hb
  simp only [eval_add, eval_mul, eval_C, eval_sub, eval_one, eval_X,
    derivative_sub, derivative_C, sub_zero, hpval]
  rcases lt_or_gt_of_ne hder with hneg | hpos
  · have h := hflux r hr hneg
    exact mul_pos_of_neg_of_neg (by linarith) hneg
  · exact mul_pos (by nlinarith [mul_pos hone hpos]) hpos

end RealRooted
