module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIClosure
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Indexed products in the positive Type-I class

Approximation on compact discs gives a local closure criterion for the positive
Type-I class. It applies to locally uniform products with arbitrary index sets,
including finite and empty products.
-/

public section

open Complex Polynomial Filter Metric Topology

namespace RealRooted

/-- Approximation by PF polynomials on every closed disc implies Type-I membership. -/
theorem IsLaguerrePolyaTypeI.of_forall_approx {f : ℂ → ℂ}
    (h : ∀ R ε : ℝ, 0 < ε → ∃ p : ℝ[X], IsPFPolynomial p ∧
      ∀ z : ℂ, ‖z‖ ≤ R → dist (f z) ((p.map ofRealHom).eval z) < ε) :
    IsLaguerrePolyaTypeI f := by
  choose P hP hd using fun n : ℕ ↦ h n (1 / (n + 1)) (by positivity)
  refine ⟨P, hP, tendstoLocallyUniformly_iff_forall_isCompact.mpr fun K hK ↦ ?_⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hK.isBounded
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop (max N ⌈R⌉₊)] with n hn x hx
  have hxR : ‖x‖ ≤ n := by
    have h1 : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp (hR hx)
    have h2 : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
    have h3 : ((⌈R⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
    linarith
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  calc
    dist (f x) ((P n).map ofRealHom |>.eval x) < 1 / (n + 1) := hd n x hxR
    _ ≤ 1 / (N + 1) := by gcongr
    _ < ε := hN

/-- A positive Type-I function is uniformly approximated by PF polynomials on
each closed disc. -/
theorem IsLaguerrePolyaTypeI.exists_approx {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], IsPFPolynomial p ∧
      ∀ z : ℂ, ‖z‖ ≤ R → dist (f z) ((p.map ofRealHom).eval z) < ε := by
  obtain ⟨P, hP, hT⟩ := hf
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp hT _
    (isCompact_closedBall (0 : ℂ) R)
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨n, hn⟩ := (hU ε hε).exists
  exact ⟨P n, hP n, fun z hz ↦ hn z (mem_closedBall_zero_iff.mpr hz)⟩

/-- The constant function one belongs to the positive Type-I class. -/
theorem IsLaguerrePolyaTypeI.one : IsLaguerrePolyaTypeI (fun _ : ℂ ↦ 1) := by
  simpa using IsPFPolynomial.one.isLaguerrePolyaTypeI

/-- Finite products preserve the positive Type-I class. -/
theorem IsLaguerrePolyaTypeI.finsetProd {ι : Type*} (s : Finset ι)
    (f : ι → ℂ → ℂ) (hf : ∀ i ∈ s, IsLaguerrePolyaTypeI (f i)) :
    IsLaguerrePolyaTypeI (fun z ↦ ∏ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsLaguerrePolyaTypeI.one
  | @insert i s hi ih =>
      simpa [Finset.prod_insert hi, Pi.mul_def] using (hf i (by simp)).mul
        (ih fun j hj ↦ hf j (by simp [hj]))

/-- An arbitrary locally uniformly convergent product of positive Type-I
functions belongs to the same class. No enumeration is required. -/
theorem IsLaguerrePolyaTypeI.of_hasProdLocallyUniformly
    {ι : Type*} {g : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hg : ∀ i, IsLaguerrePolyaTypeI (g i))
    (hprod : HasProdLocallyUniformlyOn g f Set.univ) : IsLaguerrePolyaTypeI f := by
  classical
  apply IsLaguerrePolyaTypeI.of_forall_approx
  intro R ε hε
  have hlim := tendstoLocallyUniformlyOn_univ.mp
    (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod)
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp hlim _
    (isCompact_closedBall (0 : ℂ) R)
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨s, hs⟩ := (hU (ε / 2) (half_pos hε)).exists
  obtain ⟨p, hp, hpd⟩ :=
    (IsLaguerrePolyaTypeI.finsetProd s g (fun i _ ↦ hg i)).exists_approx
      R (half_pos hε)
  refine ⟨p, hp, fun z hz ↦ ?_⟩
  calc
    dist (f z) ((p.map ofRealHom).eval z) ≤ dist (f z) (∏ i ∈ s, g i z) +
        dist (∏ i ∈ s, g i z) ((p.map ofRealHom).eval z) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hs z (mem_closedBall_zero_iff.mpr hz)) (hpd z hz)
    _ = ε := add_halves ε

end RealRooted
