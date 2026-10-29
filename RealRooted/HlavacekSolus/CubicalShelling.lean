module

public import RealRooted.HlavacekSolus.HalfOpenCube
public import RealRooted.HlavacekSolus.PolytopalShelling
import RealRooted.ReciprocalShift.ProperPosition
import RealRooted.CommonInterleaver.RootDesc
import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Algebra
import RealRooted.PolynomialValueEulerNumerator.Interlacing
import RealRooted.Transforms.BrandenE.BasisImage
import RealRooted.ChudnovskySeymour.Core

/-!
# Stable cubical shellings have real-rooted h-polynomials

M. Hlavacek and L. Solus, *Subdivisions of shellable complexes*, J. Combin. Theory Ser. A
(2021), arXiv:2003.07328, Theorem 4.1, in the abstract polytopal setting of
`RealRooted.HlavacekSolus.PolytopalShelling`:

* `cubeRelativeHRow_isInterlacingSeqNonneg`: the `2d + 1` relative h-polynomials of the
  half-open `d`-cubes form a nonnegative interlacing sequence (their Lemma 4.1; the increasing
  half is `cubeColoredEulerian_strictInterl_succ`, the reflected half
  `cubeColoredEulerian_reflect_strictInterl_succ`, both via Brändén's Theorem 4.6);
* `isRealRooted_sum_of_mem_isInterlacingSeqNonneg`: any sum of members of a nonnegative
  interlacing sequence, with repetitions, is real-rooted;
* `isRealRooted_polytopalHPolynomial_of_relativePieces_mem_cubeRelativeHRow`: a shelling whose
  relative pieces are all half-open cubes has a real-rooted h-polynomial.  The membership
  hypothesis stands in for the geometric identification of the pieces (their Lemma 3.2).
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- A list drawn with repetition from a nonnegative interlacing sequence has
a real-rooted nonzero sum whenever its sum is nonzero. -/
theorem isRealRooted_sum_of_mem_isInterlacingSeqNonneg
    {fs pieces : List ℝ[X]} (hfs : IsInterlacingSeqNonneg fs)
    (hmem : ∀ p ∈ pieces, p ∈ fs) (hsum : pieces.sum ≠ 0) :
    pieces.sum ≠ 0 ∧ pieces.sum.Splits := by
  have hpf : IsPFPolynomial
      (weightedSum (pieces.map fun p => ((1 : ℝ), p))) :=
    hfs.weightedSum_isPFPolynomial
      (pieces.map fun p => ((1 : ℝ), p))
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
        exact hmem p hp)
      (by simp)
  rw [weightedSum_map_one] at hpf
  exact hpf.ne_zero_and_splits hsum

end RealRooted

namespace RealRooted.HlavacekSolus

private lemma cayleyTransform_eq_sum {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree ≤ n) :
    Polynomial.cayleyTransform n p =
      ∑ k ∈ Finset.range (n + 1),
        C (p.coeff k) * X ^ k * (1 - X) ^ (n - k) := by
  rw [Polynomial.cayleyTransform,
    Polynomial.homogenize_eq_sum_range_C_mul_X_pow hdeg]
  simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_C]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [MvPolynomial.eval₂_X, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [← Polynomial.C_eq_algebraMap]
  ring

private lemma eval_cayleyTransform {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {x : ℝ} (hx : 1 - x ≠ 0) :
    (Polynomial.cayleyTransform n p).eval x =
      (1 - x) ^ n * p.eval (x / (1 - x)) := by
  rw [cayleyTransform_eq_sum hdeg, eval_finsetSum,
    p.eval_eq_sum_range' (n := n + 1) (by lia), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using Finset.mem_range.mp hk
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  rw [pow_sub₀ (1 - x) hx hkn, div_pow]
  field_simp

private lemma natDegree_cayleyTransform_le {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree ≤ n) :
    (Polynomial.cayleyTransform n p).natDegree ≤ n := by
  rw [cayleyTransform_eq_sum hdeg]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hkn : k ≤ n := by simpa using Finset.mem_range.mp hk
  compute_degree
  lia

private lemma eval_reflect {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree ≤ n) {x : ℝ} (hx : x ≠ 0) :
    (p.reflect n).eval x = x ^ n * p.eval (1 / x) := by
  let _ : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have h := Polynomial.eval₂_reflect_mul_pow
    (RingHom.id ℝ) x⁻¹ n p hdeg
  simp only [invOf_eq_inv] at h
  change (p.reflect n).eval (x⁻¹)⁻¹ * (x⁻¹) ^ n = p.eval x⁻¹ at h
  rw [inv_inv] at h
  have hpow : x ^ n * (x⁻¹) ^ n = 1 := by
    rw [← mul_pow]
    field_simp
    simp
  calc
    (p.reflect n).eval x =
        x ^ n * ((p.reflect n).eval x * (x⁻¹) ^ n) := by
          rw [show x ^ n * ((p.reflect n).eval x * (x⁻¹) ^ n) =
            (p.reflect n).eval x * (x ^ n * (x⁻¹) ^ n) by ring,
            hpow, mul_one]
    _ = x ^ n * p.eval x⁻¹ := by rw [h]
    _ = x ^ n * p.eval (1 / x) := by rw [one_div]

private lemma cayleyTransform_comp_neg_one_sub_X {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree ≤ n) :
    Polynomial.cayleyTransform n
        (C ((-1 : ℝ) ^ n) * p.comp (C (-1) - X)) =
      (Polynomial.cayleyTransform n p).reflect n := by
  have haffine : (C (-1) - X : ℝ[X]).natDegree ≤ 1 := by compute_degree
  have hcomp : (p.comp (C (-1) - X)).natDegree ≤ n := by
    exact Polynomial.natDegree_comp_le.trans
      ((Nat.mul_le_mul hdeg haffine).trans (by simp))
  have hleft :
      (C ((-1 : ℝ) ^ n) * p.comp (C (-1) - X)).natDegree ≤ n :=
    (Polynomial.natDegree_C_mul_le _ _).trans hcomp
  apply Polynomial.eq_of_infinite_eval_eq _ _
  refine (Set.Ioi_infinite (1 : ℝ)).mono ?_
  intro x hx
  change 1 < x at hx
  change (Polynomial.cayleyTransform n
      (C ((-1 : ℝ) ^ n) * p.comp (C (-1) - X))).eval x = _
  have hx0 : x ≠ 0 := by linarith
  have hx1 : 1 - x ≠ 0 := by linarith
  have hinv1 : 1 - x⁻¹ ≠ 0 := by
    intro h
    have : x⁻¹ = 1 := by linarith
    exact hx.ne (inv_eq_one.mp this).symm
  rw [eval_cayleyTransform hleft hx1,
    eval_reflect (natDegree_cayleyTransform_le hdeg) hx0]
  simp only [one_div]
  rw [eval_cayleyTransform hdeg hinv1]
  simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_X]
  field_simp
  have harg : (-(1 - x) - x) / (1 - x) = 1 / (x - 1) := by
    field_simp
    ring
  rw [harg]
  have hpow : x ^ n * ((x - 1) / x) ^ n =
      (-1 : ℝ) ^ n * (1 - x) ^ n := by
    rw [← mul_pow]
    have hxprod : x * ((x - 1) / x) = x - 1 := by
      field_simp
    rw [hxprod, show x - 1 = -(1 - x) by ring, neg_pow]
  rw [hpow]
  ring

private def affineFactorProduct : List ℝ → ℝ[X]
  | [] => 1
  | r :: rs => (X + C r) * affineFactorProduct rs

private lemma affineFactorProduct_monic :
    ∀ rs : List ℝ, (affineFactorProduct rs).Monic
  | [] => by simp [affineFactorProduct]
  | r :: rs => by
      rw [affineFactorProduct]
      exact (monic_X_add_C r).mul (affineFactorProduct_monic rs)

private lemma affineFactorProduct_natDegree :
    ∀ rs : List ℝ, (affineFactorProduct rs).natDegree = rs.length
  | [] => by simp [affineFactorProduct]
  | r :: rs => by
      rw [affineFactorProduct,
        natDegree_mul (monic_X_add_C r).ne_zero
          (affineFactorProduct_monic rs).ne_zero,
        natDegree_X_add_C, affineFactorProduct_natDegree]
      simp [Nat.add_comm]

private lemma brandenE_affineFactorProduct_reflect :
    ∀ rs : List ℝ,
      brandenE (affineFactorProduct (rs.map (1 - ·))) =
        C ((-1 : ℝ) ^ rs.length) *
          (brandenE (affineFactorProduct rs)).comp (C (-1) - X)
  | [] => by
      have hone : brandenE (1 : ℝ[X]) = 1 := by
        rw [show (1 : ℝ[X]) = X ^ 0 by simp, brandenE_X_pow]
        simp [orderedBellPolynomial]
      simp [affineFactorProduct, hone]
  | r :: rs => by
      simp only [List.map_cons, affineFactorProduct, List.length_cons]
      rw [brandenE_mul_X_add_C, brandenE_mul_X_add_C,
        brandenE_affineFactorProduct_reflect rs]
      change brandenEulerStep (1 - r)
          (C ((-1 : ℝ) ^ rs.length) *
            (brandenE (affineFactorProduct rs)).comp (C (-1) - X)) =
        C ((-1 : ℝ) ^ (rs.length + 1)) *
          (brandenEulerStep r (brandenE (affineFactorProduct rs))).comp
            (C (-1) - X)
      rw [brandenEulerStep_C_mul, brandenEulerStep_comp_reflect]
      rw [show (-1 : ℝ) ^ (rs.length + 1) =
        -((-1 : ℝ) ^ rs.length) by rw [pow_succ]; ring]
      have hC : C (-((-1 : ℝ) ^ rs.length)) =
          -C ((-1 : ℝ) ^ rs.length) := C_neg
      rw [hC]
      ring

private lemma polynomialValueEulerNumerator_affineFactorProduct_reflect
    (rs : List ℝ) :
    polynomialValueEulerNumerator
        (affineFactorProduct (rs.map (1 - ·))) =
      (polynomialValueEulerNumerator (affineFactorProduct rs)).reflect
        rs.length := by
  have hmaplen : (rs.map (1 - ·)).length = rs.length := by simp
  have hEdeg : (brandenE (affineFactorProduct rs)).natDegree ≤ rs.length := by
    calc
      (brandenE (affineFactorProduct rs)).natDegree ≤
          (affineFactorProduct rs).natDegree :=
        Polynomial.basisTransform_natDegree_le_of_natDegree_le
          (fun n => (orderedBellPolynomial_natDegree (R := ℝ) n).le) _
      _ = rs.length := affineFactorProduct_natDegree rs
  rw [polynomialValueEulerNumerator_eq_cayleyTransform_brandenE,
    polynomialValueEulerNumerator_eq_cayleyTransform_brandenE,
    affineFactorProduct_natDegree, affineFactorProduct_natDegree, hmaplen,
    brandenE_affineFactorProduct_reflect]
  exact cayleyTransform_comp_neg_one_sub_X hEdeg

private lemma affineFactorProduct_append (rs ss : List ℝ) :
    affineFactorProduct (rs ++ ss) =
      affineFactorProduct rs * affineFactorProduct ss := by
  induction rs with
  | nil => simp [affineFactorProduct]
  | cons r rs ih => simp [affineFactorProduct, ih, mul_assoc]

private lemma affineFactorProduct_replicate (r : ℝ) :
    ∀ n : ℕ, affineFactorProduct (List.replicate n r) = (X + C r) ^ n
  | 0 => by simp [affineFactorProduct]
  | n + 1 => by
      rw [List.replicate_succ, affineFactorProduct,
        affineFactorProduct_replicate, pow_succ']

private lemma affineFactorProduct_eq_rootPolynomial :
    ∀ rs : List ℝ, affineFactorProduct rs =
      rootPolynomial ((rs.map (-·) : List ℝ) : Multiset ℝ)
  | [] => by simp [affineFactorProduct, rootPolynomial]
  | r :: rs => by
      rw [affineFactorProduct, affineFactorProduct_eq_rootPolynomial rs]
      simp [rootPolynomial, sub_eq_add_neg]

private lemma affineFactorProduct_splits (rs : List ℝ) :
    (affineFactorProduct rs).Splits := by
  rw [affineFactorProduct_eq_rootPolynomial]
  exact rootPolynomial_splits _

private lemma affineFactorProduct_rootwiseLE_zero (rs : List ℝ)
    (hrs : ∀ r ∈ rs, 0 ≤ r) :
    RootwiseLE (affineFactorProduct rs)
      (affineFactorProduct (List.replicate rs.length 0)) := by
  unfold RootwiseLE
  rw [affineFactorProduct_eq_rootPolynomial,
    affineFactorProduct_eq_rootPolynomial, roots_rootPolynomial,
    roots_rootPolynomial]
  apply List.forall₂_of_length_eq_of_get
  · simp
  intro i hi_left hi_right
  have hleft_mem :
      (((((rs.map (-·) : List ℝ) : Multiset ℝ).sort (· ≤ ·))[i]) ∈
        ((rs.map (-·) : List ℝ) : Multiset ℝ)) := by
    exact (Multiset.mem_sort _).mp (List.getElem_mem hi_left)
  have hright_mem :
      ((((((List.replicate rs.length 0).map (-·) : List ℝ) :
        Multiset ℝ).sort (· ≤ ·))[i]) ∈
        (((List.replicate rs.length 0).map (-·) : List ℝ) :
          Multiset ℝ)) := by
    exact (Multiset.mem_sort _).mp (List.getElem_mem hi_right)
  simp only [Multiset.mem_coe, List.mem_map] at hleft_mem
  obtain ⟨r, hr, hri⟩ := hleft_mem
  simp only [Multiset.mem_coe, List.mem_map] at hright_mem
  obtain ⟨s, hs, hsi⟩ := hright_mem
  have hs0 : s = 0 := (by simpa using hs : rs ≠ [] ∧ s = 0).2
  subst s
  calc
    ((((rs.map (-·) : List ℝ) : Multiset ℝ).sort (· ≤ ·))[i]) =
        -r := hri.symm
    _ ≤ 0 := neg_nonpos.mpr (hrs r hr)
    _ = (((((List.replicate rs.length 0).map (-·) : List ℝ) :
        Multiset ℝ).sort (· ≤ ·))[i]) := by simpa using hsi

private lemma affineFactorProduct_roots_mem_Icc (rs : List ℝ)
    (hrs : ∀ r ∈ rs, r ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x ∈ (affineFactorProduct rs).roots,
      x ∈ Set.Icc (-1 : ℝ) 0 := by
  intro x hx
  rw [affineFactorProduct_eq_rootPolynomial, roots_rootPolynomial,
    Multiset.mem_coe, List.mem_map] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  have h := hrs r hr
  constructor <;> linarith [h.1, h.2]

private lemma polynomialValueEulerNumerator_cube_midpoint_monic
    {d : ℕ} (hd : 0 < d) :
    StrictInterl
      (polynomialValueEulerNumerator
        ((X + 1) ^ (d - 1) * (X + C (1 / 2 : ℝ))))
      (polynomialValueEulerNumerator (X ^ d)) := by
  let rs := List.replicate (d - 1) 1 ++ [(1 / 2 : ℝ)]
  have hrslen : rs.length = d := by
    simp [rs]
    lia
  have hrs_nonneg : ∀ r ∈ rs, 0 ≤ r := by
    intro r hr
    simp only [rs, List.mem_append, List.mem_replicate, List.mem_singleton] at hr
    rcases hr with ⟨_, rfl⟩ | rfl <;> norm_num
  have hrs_Icc : ∀ r ∈ rs, r ∈ Set.Icc (0 : ℝ) 1 := by
    intro r hr
    simp only [rs, List.mem_append, List.mem_replicate, List.mem_singleton] at hr
    rcases hr with ⟨_, rfl⟩ | rfl <;> norm_num
  have hleft : affineFactorProduct rs =
      (X + 1) ^ (d - 1) * (X + C (1 / 2 : ℝ)) := by
    dsimp [rs]
    rw [affineFactorProduct_append, affineFactorProduct_replicate]
    simp [affineFactorProduct]
  have hright : affineFactorProduct (List.replicate rs.length 0) = X ^ d := by
    rw [affineFactorProduct_replicate, hrslen]
    simp
  have hright_Icc : ∀ r ∈ List.replicate rs.length (0 : ℝ),
      r ∈ Set.Icc (0 : ℝ) 1 := by simp
  have hW := polynomialValueEulerNumerator_strictInterl_of_rootwiseLE
    (affineFactorProduct_monic rs)
    (affineFactorProduct_monic (List.replicate rs.length 0))
    (affineFactorProduct_splits rs)
    (affineFactorProduct_splits (List.replicate rs.length 0))
    (affineFactorProduct_natDegree rs)
    (by simpa using
      affineFactorProduct_natDegree (List.replicate rs.length 0))
    (by simpa [hrslen] using hd.ne')
    (affineFactorProduct_roots_mem_Icc rs hrs_Icc)
    (affineFactorProduct_roots_mem_Icc _ hright_Icc)
    (affineFactorProduct_rootwiseLE_zero rs hrs_nonneg)
  rw [hleft, hright] at hW
  exact hW

private def cubeMonicSource (d l : ℕ) : ℝ[X] :=
  X ^ l * (X + C (1 / 2 : ℝ)) ^ (d - l)

private lemma cubeValuePolynomial_eq_C_mul_monic {d l : ℕ} (hl : l ≤ d) :
    cubeValuePolynomial d l = C (2 ^ d : ℝ) * cubeMonicSource d l := by
  have hfactor : C 2 * X + 1 = C 2 * (X + C (1 / 2 : ℝ)) := by
    rw [mul_add, ← C_mul]
    norm_num
  rw [cubeValuePolynomial_def]
  unfold cubeMonicSource
  rw [hfactor, mul_pow, mul_pow, ← C_pow, ← C_pow]
  calc
    (C (2 ^ l : ℝ) * X ^ l) *
        (C (2 ^ (d - l) : ℝ) * (X + C (1 / 2 : ℝ)) ^ (d - l)) =
        C ((2 : ℝ) ^ l * 2 ^ (d - l)) *
          (X ^ l * (X + C (1 / 2 : ℝ)) ^ (d - l)) := by
            rw [C_mul]
            ring
    _ = C (2 ^ d : ℝ) *
        (X ^ l * (X + C (1 / 2 : ℝ)) ^ (d - l)) := by
          rw [← pow_add, Nat.add_sub_of_le hl]

private lemma cubeColoredEulerian_eq_C_mul_monic {d l : ℕ} (hl : l ≤ d) :
    cubeColoredEulerian d l =
      C (2 ^ d : ℝ) * polynomialValueEulerNumerator (cubeMonicSource d l) := by
  rw [cubeColoredEulerian_def, cubeValuePolynomial_eq_C_mul_monic hl,
    polynomialValueEulerNumerator_C_mul (by positivity)]

private lemma cubeMonicSource_reflect {d l : ℕ} (hl : l ≤ d) :
    polynomialValueEulerNumerator
        ((X + 1) ^ l * (X + C (1 / 2 : ℝ)) ^ (d - l)) =
      (polynomialValueEulerNumerator (cubeMonicSource d l)).reflect d := by
  let rs := List.replicate l 0 ++ List.replicate (d - l) (1 / 2 : ℝ)
  have hrslen : rs.length = d := by
    simp [rs]
    lia
  have hprod : affineFactorProduct rs = cubeMonicSource d l := by
    dsimp [rs]
    rw [affineFactorProduct_append, affineFactorProduct_replicate,
      affineFactorProduct_replicate]
    simp [cubeMonicSource]
  have hmapped : affineFactorProduct (rs.map (1 - ·)) =
      (X + 1) ^ l * (X + C (1 / 2 : ℝ)) ^ (d - l) := by
    dsimp [rs]
    rw [List.map_append, List.map_replicate, List.map_replicate,
      affineFactorProduct_append, affineFactorProduct_replicate,
      affineFactorProduct_replicate]
    norm_num
  rw [← hmapped, polynomialValueEulerNumerator_affineFactorProduct_reflect,
    hprod, hrslen]

private lemma cubeColoredEulerian_reflect {d l : ℕ} (hl : l ≤ d) :
    (cubeColoredEulerian d l).reflect d =
      C (2 ^ d : ℝ) * polynomialValueEulerNumerator
        ((X + 1) ^ l * (X + C (1 / 2 : ℝ)) ^ (d - l)) := by
  rw [cubeColoredEulerian_eq_C_mul_monic hl, Polynomial.reflect_C_mul,
    ← cubeMonicSource_reflect hl]

private lemma cubeColoredEulerian_zero_reflect (d : ℕ) :
    (cubeColoredEulerian d 0).reflect d = cubeColoredEulerian d 0 := by
  rw [cubeColoredEulerian_reflect (Nat.zero_le d),
    cubeColoredEulerian_eq_C_mul_monic (Nat.zero_le d)]
  simp [cubeMonicSource]

private lemma cubeColoredEulerian_reflect_pred_strictInterl_last
    {d : ℕ} (hd : 0 < d) :
    StrictInterl ((cubeColoredEulerian d (d - 1)).reflect d)
      (cubeColoredEulerian d d) := by
  have hW := polynomialValueEulerNumerator_cube_midpoint_monic hd
  have hscaled := (hW.C_mul_left (by positivity : (2 ^ d : ℝ) ≠ 0)).C_mul_right
    (by positivity : (2 ^ d : ℝ) ≠ 0)
  have hreflect := cubeColoredEulerian_reflect (show d - 1 ≤ d by lia)
  have hlast := cubeColoredEulerian_eq_C_mul_monic (show d ≤ d by lia)
  rw [show d - (d - 1) = 1 by lia] at hreflect
  simp only [pow_one] at hreflect
  simp only [cubeMonicSource, Nat.sub_self, pow_zero, mul_one] at hlast
  rw [hreflect, hlast]
  simpa only [C_pow] using hscaled

private lemma cubeColoredEulerian_last_strictInterl_X_reflect_pred
    {d : ℕ} (hd : 0 < d) :
    StrictInterl (cubeColoredEulerian d d)
      (X * (cubeColoredEulerian d (d - 1)).reflect d) := by
  exact strictInterl_mul_X_of_strictInterl_of_nonneg
    (cubeColoredEulerian_reflect_pred_strictInterl_last hd)
    ((cubeColoredEulerian_nonneg d (d - 1)).reflect d)
    (cubeColoredEulerian_nonneg d d)

private lemma cubeColoredEulerian_zero_strictInterl_X_reflect (d : ℕ) :
    StrictInterl (cubeColoredEulerian d 0)
      (X * (cubeColoredEulerian d 0).reflect d) := by
  rw [cubeColoredEulerian_zero_reflect]
  exact strictInterl_self_X_mul_of_nonneg
    (cubeColoredEulerian_ne_zero_and_splits d 0).1
    (cubeColoredEulerian_ne_zero_and_splits d 0).2
    (cubeColoredEulerian_nonneg d 0)


/-- Consecutive members of the reflected half of the cube row interlace in
the reversed index order. -/
theorem cubeColoredEulerian_reflect_strictInterl_succ {d l : ℕ}
    (hl : l + 1 ≤ d) :
    StrictInterl
      (X * (cubeColoredEulerian d (l + 1)).reflect d)
      (X * (cubeColoredEulerian d l).reflect d) := by
  have hreflect := reciprocalShift_reverses_strictInterl
    (cubeColoredEulerian_isPFPolynomial d l)
    (cubeColoredEulerian_isPFPolynomial d (l + 1))
    (cubeColoredEulerian_natDegree_le (by lia))
    (cubeColoredEulerian_natDegree_le hl)
    (cubeColoredEulerian_strictInterl_succ hl)
  simpa only [reciprocalShift, map_zero, sub_zero] using
    hreflect.mul_X_sub_C_both 0

private lemma cubeRelativeHPolynomial_strictInterl_succ
    {d l : ℕ} (hl : l < 2 * d) :
    StrictInterl (cubeRelativeHPolynomial d l)
      (cubeRelativeHPolynomial d (l + 1)) := by
  by_cases hleft : l < d
  · rw [cubeRelativeHPolynomial_of_le (by lia),
      cubeRelativeHPolynomial_of_le (by lia)]
    exact cubeColoredEulerian_strictInterl_succ (by lia)
  by_cases hmiddle : l = d
  · subst l
    rw [cubeRelativeHPolynomial_of_le (by lia),
      cubeRelativeHPolynomial_of_lt (by lia)]
    rw [show 2 * d - (d + 1) = d - 1 by lia]
    exact cubeColoredEulerian_last_strictInterl_X_reflect_pred (by lia)
  · have hright : d < l := by lia
    rw [cubeRelativeHPolynomial_of_lt hright,
      cubeRelativeHPolynomial_of_lt (by lia)]
    let k := 2 * d - (l + 1)
    have hk_succ : k + 1 = 2 * d - l := by
      dsimp [k]
      lia
    have hk_le : k + 1 ≤ d := by
      dsimp [k]
      lia
    have hreflect := cubeColoredEulerian_reflect_strictInterl_succ
      (d := d) (l := k) hk_le
    rw [hk_succ] at hreflect
    exact hreflect

private lemma cubeRelativeHPolynomial_endpoint {d : ℕ} (hd : 0 < d) :
    StrictInterl (cubeRelativeHPolynomial d 0)
      (cubeRelativeHPolynomial d (2 * d)) := by
  rw [cubeRelativeHPolynomial_of_le (Nat.zero_le d),
    cubeRelativeHPolynomial_of_lt (by lia)]
  simp only [Nat.sub_self]
  exact cubeColoredEulerian_zero_strictInterl_X_reflect d

/-- The relative h-polynomials of all half-open `d`-cubes form a
nonnegative interlacing sequence in admissible facet order. -/
theorem cubeRelativeHRow_isInterlacingSeqNonneg (d : ℕ) :
    IsInterlacingSeqNonneg (cubeRelativeHRow d) := by
  refine ⟨cubeRelativeHRow_realRooted_nonneg d, ?_⟩
  rw [isInterlacingSeq_iff_pairwise, cubeRelativeHRow_def]
  refine List.pairwise_ofFn.2 ?_
  intro i j hij
  by_cases hd : d = 0
  · subst d
    have hi := i.isLt
    have hj := j.isLt
    have hij' : i.val < j.val := hij
    exfalso
    lia
  · exact strictInterl_chain_of_consecutive_of_endpoint
      (cubeRelativeHPolynomial d) 0 (2 * d)
      (fun k _ hk => cubeRelativeHPolynomial_strictInterl_succ hk)
      (cubeRelativeHPolynomial_endpoint (Nat.pos_of_ne_zero hd))
      i j (Nat.zero_le i) hij.le (by lia)

/-- A stable cubical shelling has a real-rooted h-polynomial when every
relative piece has a half-open cube relative h-polynomial.

The membership hypothesis is the abstract stand-in for the geometric
identification of each relative piece with a half-open cube in
Hlavacek--Solus, Lemma 3.2 and Theorem 4.1.
-/
theorem isRealRooted_polytopalHPolynomial_of_relativePieces_mem_cubeRelativeHRow
    {α : Type*} [DecidableEq α] (d : ℕ) (C : PolytopalFaceData α)
    (sh : PolytopalShelling C)
    (hmem : ∀ p ∈ polytopalRelativeHPolynomials d C sh,
      p ∈ cubeRelativeHRow d)
    (hpoly_ne : polytopalHPolynomial d C.rank C.faces ≠ 0) :
    polytopalHPolynomial d C.rank C.faces ≠ 0 ∧
      (polytopalHPolynomial d C.rank C.faces).Splits := by
  rw [polytopalHPolynomial_eq_sum_relativePieces d C sh] at hpoly_ne ⊢
  exact isRealRooted_sum_of_mem_isInterlacingSeqNonneg
    (cubeRelativeHRow_isInterlacingSeqNonneg d) hmem hpoly_ne

end RealRooted.HlavacekSolus
