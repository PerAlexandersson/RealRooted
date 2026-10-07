import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya

/-!
# Closure of the Laguerre–Pólya class under locally uniform limits

`IsLaguerrePolya f` asks for real-rooted polynomials converging to `f` locally uniformly.
Equivalently (`IsLaguerrePolya.of_forall_approx`, `IsLaguerrePolya.exists_approx`), on every
disc `f` is uniformly approximable by such polynomials.  A diagonal argument then shows that
the class is closed under locally uniform limits (`IsLaguerrePolya.of_tendstoLocallyUniformly`).
-/

open Polynomial Filter

namespace RealRooted

/-- Approximation criterion: `f` is in the Laguerre–Pólya class as soon as it can be
approximated uniformly on every closed disc centred at `0` by real-rooted real polynomials. -/
theorem IsLaguerrePolya.of_forall_approx {f : ℂ → ℂ}
    (h : ∀ R ε : ℝ, 0 < ε → ∃ p : ℝ[X], (p = 0 ∨ p.Splits) ∧
      ∀ z : ℂ, ‖z‖ ≤ R → dist (f z) ((p.map Complex.ofRealHom).eval z) < ε) :
    IsLaguerrePolya f := by
  choose P hP hd using fun n : ℕ => h n (1 / (n + 1)) (by positivity)
  refine ⟨P, hP, tendstoLocallyUniformly_iff_forall_isCompact.mpr fun K hK => ?_⟩
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
  calc dist (f x) ((P n).map Complex.ofRealHom |>.eval x) < 1 / (n + 1) := hd n x hxR
    _ ≤ 1 / (N + 1) := by gcongr
    _ < ε := hN

/-- A function in the Laguerre–Pólya class is approximated uniformly on every closed disc
centred at `0` by real-rooted real polynomials. -/
theorem IsLaguerrePolya.exists_approx {f : ℂ → ℂ} (hf : IsLaguerrePolya f) (R : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ p : ℝ[X], (p = 0 ∨ p.Splits) ∧
      ∀ z : ℂ, ‖z‖ ≤ R → dist (f z) ((p.map Complex.ofRealHom).eval z) < ε := by
  obtain ⟨P, hP, hT⟩ := hf
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp hT _
    (isCompact_closedBall (0 : ℂ) R)
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨n, hn⟩ := (hU ε hε).exists
  exact ⟨P n, hP n, fun z hz => hn z (mem_closedBall_zero_iff.mpr hz)⟩

/-- The Laguerre–Pólya class is closed under locally uniform limits of sequences. -/
theorem IsLaguerrePolya.of_tendstoLocallyUniformly {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ m, IsLaguerrePolya (F m)) (h : TendstoLocallyUniformly F f atTop) :
    IsLaguerrePolya f := by
  refine IsLaguerrePolya.of_forall_approx fun R ε hε => ?_
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp h _
    (isCompact_closedBall (0 : ℂ) R)
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨m, hm⟩ := (hU (ε / 2) (half_pos hε)).exists
  obtain ⟨p, hp, hpd⟩ := (hF m).exists_approx R (half_pos hε)
  refine ⟨p, hp, fun z hz => ?_⟩
  calc dist (f z) ((p.map Complex.ofRealHom).eval z)
      ≤ dist (f z) (F m z) + dist (F m z) ((p.map Complex.ofRealHom).eval z) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hm z (mem_closedBall_zero_iff.mpr hz)) (hpd z hz)
    _ = ε := add_halves ε


end RealRooted
