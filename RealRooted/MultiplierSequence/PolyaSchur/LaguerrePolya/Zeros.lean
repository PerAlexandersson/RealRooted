import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative

/-!
# Real zeros of Laguerre--Pólya limits

This leaf proves the real-zero closure special to locally uniform limits of
real splitting polynomials. It is not a general Hurwitz or Rouché theorem.
-/

open Complex Filter Polynomial Topology

noncomputable section

namespace Polynomial

private theorem nnnorm_aeval_of_splits (p : ℝ[X]) (z : ℂ) (hp : p.Splits) :
    ‖aeval z p‖₊ = ‖(p.leadingCoeff : ℂ)‖₊ *
      (Multiset.map (fun r : ℝ => ‖z - (r : ℂ)‖₊) p.roots).prod := by
  have h1 : (aeval z) ((Multiset.map (fun x : ℝ => X - C x) p.roots).prod)
      = (Multiset.map (fun r : ℝ => z - (r : ℂ)) p.roots).prod := by
    rw [map_multiset_prod]
    simp [Multiset.map_map]
  have h2 : ‖(Multiset.map (fun r : ℝ => z - (r : ℂ)) p.roots).prod‖₊
      = (Multiset.map (fun r : ℝ => ‖z - (r : ℂ)‖₊) p.roots).prod := by
    simpa [Multiset.map_map, Function.comp_def] using
      map_multiset_prod (nnnormHom (α := ℂ))
        (Multiset.map (fun r : ℝ => z - (r : ℂ)) p.roots)
  conv_lhs => rw [hp.eq_prod_roots]
  rw [map_mul, h1, nnnorm_mul, h2]
  simp

/-- Along a vertical line, the norm of a real splitting polynomial is
nondecreasing with the absolute value of the imaginary part. -/
theorem norm_aeval_mono_im_of_splits {p : ℝ[X]} (hp : p.Splits) (x y y' : ℝ)
    (h : |y'| ≤ |y|) :
    ‖aeval ((x : ℂ) + y' * I) p‖ ≤ ‖aeval ((x : ℂ) + y * I) p‖ := by
  have hsq : y' ^ 2 ≤ y ^ 2 := by
    nlinarith [sq_abs y, sq_abs y', abs_nonneg y', abs_nonneg y]
  rw [← coe_nnnorm, ← coe_nnnorm, NNReal.coe_le_coe,
    nnnorm_aeval_of_splits p _ hp, nnnorm_aeval_of_splits p _ hp]
  gcongr
  refine Multiset.prod_map_le_prod_map _ _ (fun r _ => ?_)
  rw [← NNReal.coe_le_coe]
  simp only [coe_nnnorm, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp [Complex.normSq_apply]
  nlinarith

private theorem eval_map_ofRealHom (p : ℝ[X]) (z : ℂ) :
    (p.map Complex.ofRealHom).eval z = aeval z p := by
  have hmap : Complex.ofRealHom = algebraMap ℝ ℂ := rfl
  rw [hmap, eval_map, aeval_def]

end Polynomial

namespace RealRooted

/-- A nonzero Laguerre--Pólya limit has only real complex zeros. This is the
special vertical-modulus argument for real splitting polynomial approximants,
not a general Hurwitz theorem. -/
theorem IsLaguerrePolya.im_eq_zero_of_eq_zero {f : ℂ → ℂ} (hf : IsLaguerrePolya f)
    (hne : f ≠ 0) {z : ℂ} (hz : f z = 0) :
    z.im = 0 := by
  have hana : AnalyticOnNhd ℂ f Set.univ := IsLaguerrePolya.analyticOnNhd hf
  obtain ⟨p, hp, hconv⟩ := hf
  have hconv' := tendstoLocallyUniformlyOn_univ.mpr hconv
  have hsplit : ∀ n, (p n).Splits := by
    intro n
    rcases hp n with hzero | hsplit
    · rw [hzero]
      exact Splits.zero
    · exact hsplit
  have hmono : ∀ x y y' : ℝ, |y'| ≤ |y| →
      ‖f ((x : ℂ) + y' * I)‖ ≤ ‖f ((x : ℂ) + y * I)‖ := fun x y y' h =>
    le_of_tendsto_of_tendsto'
      ((hconv'.tendsto_at (Set.mem_univ _)).norm)
      ((hconv'.tendsto_at (Set.mem_univ _)).norm)
      (fun n => by
        simpa only [Polynomial.eval_map_ofRealHom] using
          Polynomial.norm_aeval_mono_im_of_splits (hsplit n) x y y' h)
  by_contra him
  set x := z.re with hx
  set y₀ := z.im with hy
  have hzeq : ((x : ℂ) + y₀ * I) = z := by
    apply Complex.ext <;> simp [hx, hy]
  have hseg : ∀ y : ℝ, |y| ≤ |y₀| → f ((x : ℂ) + y * I) = 0 := by
    intro y hy'
    have hle := hmono x y₀ y hy'
    rw [hzeq, hz] at hle
    simpa using hle
  have hfreq : ∃ᶠ w in 𝓝[≠] (x : ℂ), f w = 0 := by
    have htend : Tendsto
        (fun n : ℕ => (x : ℂ) + ((y₀ / (n + 1) : ℝ) : ℂ) * I) atTop
        (𝓝[≠] (x : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hzero : Tendsto (fun n : ℕ => (y₀ / (n + 1) : ℝ)) atTop (𝓝 0) := by
          simpa using tendsto_const_nhds.div_atTop
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        have hmap := (Complex.continuous_ofReal.tendsto 0).comp hzero
        simpa using (tendsto_const_nhds (x := (x : ℂ)) (f := atTop)).add (hmap.mul_const I)
      · filter_upwards with n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hcon
        have himag := congrArg Complex.im hcon
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
          Complex.ofReal_re, zero_add] at himag
        rcases div_eq_zero_iff.mp himag with hzero | hdenom
        · exact him hzero
        · exact absurd hdenom (by positivity)
    refine htend.frequently (Eventually.frequently ?_)
    filter_upwards with n
    refine hseg _ ?_
    rw [abs_div, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg y₀, Nat.cast_nonneg (α := ℝ) n,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)]
  exact hne (funext fun w => hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ _) hfreq (Set.mem_univ w))

end RealRooted
