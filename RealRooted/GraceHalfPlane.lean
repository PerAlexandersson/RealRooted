import RealRooted.Apolarity
import Mathlib.Analysis.Complex.Convex

open Polynomial Complex

namespace RealRooted

def lowerHalf (b : ℝ) : Set ℂ := {z : ℂ | z.im ≤ b}

@[simp] theorem mem_lowerHalf {b : ℝ} {z : ℂ} : z ∈ lowerHalf b ↔ z.im ≤ b := Iff.rfl

theorem convex_lowerHalf (b : ℝ) : Convex ℝ (lowerHalf b) :=
  convex_halfSpace_im_le b

theorem mem_lowerHalf_of_recip_avg {b : ℝ} {w ζ : ℂ}
    (S : Multiset ℂ) (hS : S ≠ 0)
    (hw : w ∉ lowerHalf b)
    (hz : ∀ z ∈ S, z ∈ lowerHalf b)
    (hζ : (S.card : ℂ) / (w - ζ) = (S.map (fun z ↦ 1 / (w - z))).sum) :
    ζ ∈ lowerHalf b := by
  have hA_pos : 0 < w.im - b := by simp_all
  set A : ℝ := w.im - b with hA
  set K : Set ℂ := {u : ℂ | A * Complex.normSq u + u.im ≤ 0} with hK
  have : 0 < 2 * A := by linarith
  have hrad : (0 : ℝ) ≤ 1 / (2 * A) := by positivity
  have hKeq : K = Metric.closedBall (Complex.mk 0 (-(1 / (2 * A)))) (1 / (2 * A)) := by
    ext u
    simp only [hK, Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm,
      Complex.norm_def, Real.sqrt_le_left hrad, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im]
    rw [show (u.re - 0) * (u.re - 0)
          + (u.im - -(1 / (2 * A))) * (u.im - -(1 / (2 * A)))
        = (A * (u.re * u.re + u.im * u.im) + u.im) / A + (1 / (2 * A)) ^ 2 by
      grind]
    have : (0:ℝ) < 1 / A := by positivity
    constructor
    · intro h
      have hle : (A * (u.re * u.re + u.im * u.im) + u.im) / A ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg h (le_of_lt hA_pos)
      simp_all
    · intro h
      have hle : (A * (u.re * u.re + u.im * u.im) + u.im) / A ≤ 0 := by simp_all
      have := (div_nonpos_iff.mp hle)
      grind
  have hK_convex : Convex ℝ K := by rw [hKeq]; exact convex_closedBall _ _
  have : ∀ z : ℂ, w - z ≠ 0 → (z ∈ lowerHalf b ↔ (1 / (w - z)) ∈ K) := by
    intro z hwz
    have hnsq : 0 < Complex.normSq (w - z) := Complex.normSq_pos.mpr hwz
    have himeq : (1 / (w - z)).im = -(w.im - z.im) / Complex.normSq (w - z) := by simp
    have hnsq_mk : Complex.normSq (1 / (w - z)) = 1 / Complex.normSq (w - z) := by simp
    simp only [mem_lowerHalf, hK, Set.mem_setOf_eq]
    rw [himeq, hnsq_mk, mul_one_div]
    rw [← add_div, div_nonpos_iff]
    grind
  have : ∀ z ∈ S, (1 / (w - z)) ∈ K := by grind
  set T : Multiset ℂ := S.map (fun z ↦ 1 / (w - z)) with hT
  have hT_ne : T ≠ 0 := by simp [*]
  have : ∀ u ∈ T, u ∈ K := by simp_all
  have : T.card = S.card := by simp [*]
  have : T.sum / (T.card : ℂ) ∈ K := by
    rw [hKeq]
    exact multiset_avg_mem_closedBall T hT_ne (by simp_all)
  have hrecip_im_neg : ∀ u ∈ T, u.im < 0 := by
    intro u hu
    rw [hT, Multiset.mem_map] at hu
    obtain ⟨z, hzS, rfl⟩ := hu
    have hwz : w - z ≠ 0 := by grind
    have hnsq : 0 < Complex.normSq (w - z) := Complex.normSq_pos.mpr hwz
    have : z.im ≤ b := hz z hzS
    have : b < w.im := by simp_all
    rw [one_div, Complex.inv_im, Complex.sub_im]
    apply div_neg_of_neg_of_pos _ hnsq
    grind
  have : T.sum.im < 0 := by
    have hmap : T.sum.im = (T.map (fun u ↦ u.im)).sum := by
      have := map_multiset_sum Complex.imAddGroupHom T
      simp_all
    rw [hmap]
    have hlt : (T.map (fun u ↦ u.im)).sum < (T.map (fun _ : ℂ ↦ (0:ℝ))).sum :=
      Multiset.sum_lt_sum_of_nonempty hT_ne hrecip_im_neg
    simpa using hlt
  have : T.sum ≠ 0 := by
    intro h
    simp_all
  grind

theorem multiset_avg_mem_lowerHalf {b : ℝ} (S : Multiset ℂ) (hS : S ≠ 0)
    (hz : ∀ z ∈ S, z ∈ lowerHalf b) :
    S.sum / (S.card : ℂ) ∈ lowerHalf b := by
  have : 0 < S.card := Multiset.card_pos.mpr hS
  have hcardℝ : (0 : ℝ) < (S.card : ℝ) := by simp [*]
  have hsum_im : S.sum.im = (S.map (fun z ↦ z.im)).sum := by
    have := map_multiset_sum Complex.imAddGroupHom S
    simp_all
  have : S.sum.im ≤ b * (S.card : ℝ) := by
    rw [hsum_im]
    have : (S.map (fun z ↦ z.im)).sum ≤ (S.map (fun _ : ℂ ↦ b)).sum :=
      Multiset.sum_map_le_sum_map _ _ (fun z hzS ↦ hz z hzS)
    have : (S.map (fun _ : ℂ ↦ b)).sum = b * (S.card : ℝ) := by
      rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_comm]
    simp_all
  have hquot_im : (S.sum / (S.card : ℂ)).im = S.sum.im / (S.card : ℝ) := by simp
  simp only [mem_lowerHalf, hquot_im]
  rw [div_le_iff₀ hcardℝ]
  simp_all

theorem polarDeriv_rootsIn_lowerHalf {n : Nat} {b : ℝ} {ζ : ℂ}
    {A : ℂ[X]} (hn : 1 ≤ n) (hA : A.natDegree = n)
    (hAroots : A.RootsIn (lowerHalf b))
    (hζ : ζ ∉ lowerHalf b) :
    (polarDeriv n ζ A).RootsIn (lowerHalf b) := by
  intro w hw0
  by_contra hwmem
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero_of_pos (R := ℂ) (by lia)
  have hAw : eval w A ≠ 0 := fun h ↦ hwmem (hAroots w h)
  have : (n : ℂ) * eval w A + (ζ - w) * eval w (derivative A) = 0 := by
    have h := hw0
    simp only [IsRoot, polarDeriv, eval_add, eval_mul, eval_sub, eval_C, eval_X] at h
    simp_all
  have hwζ : w - ζ ≠ 0 := by grind
  have hsplit : A.Splits := IsAlgClosed.splits A
  have hcard : A.roots.card = n := (splits_iff_card_roots.mp hsplit).trans hA
  have : eval w (derivative A) / eval w A
      = (A.roots.map (fun z ↦ 1 / (w - z))).sum :=
    hsplit.eval_derivative_div_eval_of_ne_zero hAw
  have : eval w (derivative A) / eval w A = (n : ℂ) / (w - ζ) := by grind
  have hζeq : (A.roots.card : ℂ) / (w - ζ)
      = (A.roots.map (fun z ↦ 1 / (w - z))).sum := by simp_all
  have : ζ ∈ lowerHalf b := by
    refine mem_lowerHalf_of_recip_avg A.roots ?_ hwmem ?_ hζeq
    · rw [← Multiset.card_pos, hcard]; grind
    · exact fun z hz ↦ hAroots z (isRoot_of_mem_roots hz)
  simp_all

theorem polarDeriv_natDegree_lowerHalf {n : Nat} {b : ℝ} {ζ : ℂ}
    {A : ℂ[X]} (hn : 1 ≤ n) (hA : A.natDegree = n)
    (hAroots : A.RootsIn (lowerHalf b))
    (hζ : ζ ∉ lowerHalf b) :
    (polarDeriv n ζ A).natDegree = n - 1 := by
  refine le_antisymm ?_ ?_
  · rw [Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero]
    unfold polarDeriv
    simp_all +decide only [Nat.cast_lt, map_natCast, coeff_add,
      coeff_natCast_mul]
    intro m hm
    rcases m with (_ | m) <;>
      simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_derivative,
        sub_mul ]
    cases hm.eq_or_lt <;> simp_all [Polynomial.coeff_eq_zero_of_natDegree_lt]
    grind
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    have : (polarDeriv n ζ A).coeff (n - 1)
        = A.coeff n * ((n : ℂ) * ζ - Multiset.sum A.roots) := by
      have : (polarDeriv n ζ A).coeff (n - 1)
          = ((n : ℂ) - (n - 1)) * A.coeff (n - 1) + ζ * (n : ℂ) * A.coeff n := by
        unfold polarDeriv
        simp only [mul_assoc, sub_mul, map_natCast, coeff_add, coeff_natCast_mul,
          sub_sub_cancel, one_mul]
        rcases n with (_ | _ | n) <;>
          simp_all [Polynomial.coeff_derivative, mul_comm]
        grind
      have : A.coeff (n - 1)
          = A.leadingCoeff * (-1) ^ (n - (n - 1)) * Multiset.esymm A.roots (n - (n - 1)) := by
        have h_eq := Polynomial.coeff_eq_esymm_roots_of_card
          (splits_iff_card_roots.mp (IsAlgClosed.splits A))
          (show n - 1 ≤ A.natDegree by lia)
        rw [hA] at h_eq
        exact h_eq
      rcases n with (_ | _ | n) <;> simp_all [Multiset.esymm]
      · simp_all [Multiset.powersetCard_one, mul_sub] ; ring_nf
        rw [Polynomial.leadingCoeff, hA]
        grind
      · simp_all [Multiset.powersetCard_one, Polynomial.leadingCoeff] ; grind
    simp_all only [ne_eq]
    refine mul_ne_zero ?_ ?_
    · rw [← hA, Polynomial.coeff_natDegree] ; aesop
    · intro h
      rw [sub_eq_zero] at h
      have h_avg : A.roots.sum / (A.roots.card : ℂ) ∈ lowerHalf b := by
        apply multiset_avg_mem_lowerHalf
        · rw [← Multiset.card_pos]
          rw [Polynomial.splits_iff_card_roots.mp <| IsAlgClosed.splits A, hA]
          linarith
        · exact fun z hz ↦ hAroots z <| Polynomial.isRoot_of_mem_roots hz
      rw [← h, mul_div_assoc] at h_avg
      rw [ show A.roots.card = n by
        rw [ ← hA, Polynomial.natDegree_eq_of_degree_eq_some
          ( Polynomial.degree_eq_natDegree <| by
            subst hA
            simp_all only [mem_lowerHalf, not_le, coeff_natDegree, sub_self, mul_zero,
              mul_im, natCast_re, div_natCast_im, natCast_im, div_natCast_re, zero_mul,
              add_zero, ne_eq]
            apply Aesop.BuiltinRules.not_intro
            intro a
            simp_all ) ]
        exact Polynomial.splits_iff_card_roots.mp <| IsAlgClosed.splits _ ] at h_avg
      simp_all [mul_div_cancel₀, ne_of_gt (zero_lt_one.trans_le hn)]
      linarith

private theorem grace_aux_lowerHalf {b : ℝ} :
    ∀ (n : Nat) (f g : ℂ[X]),
      (binomialLift n f).natDegree = n → (binomialLift n g).natDegree = n →
      AreApolar n f g → (binomialLift n f).RootsIn (lowerHalf b) →
      (binomialLift n g).HasRootIn (lowerHalf b) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih f g hf hg hap hroots
  by_cases hn : n = 0
  · subst hn
    by_cases h : g.coeff 0 = 0
    · refine ⟨Complex.mk 0 b, ?_, ?_⟩ <;> simp_all [binomialLift]
    · have h_contra : f.coeff 0 = 0 := by
        unfold AreApolar at hap
        simp [apolarPairing] at hap
        simp_all
      contrapose! hroots
      unfold RootsIn
      simp_all only [IsRoot.def, mem_lowerHalf, not_forall, not_le]
      refine ⟨Complex.mk 0 (b + 1), ?_, ?_⟩
      · simp [h_contra, binomialLift]
      · simp
  · obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, (binomialLift n g).IsRoot ζ := by
      exact Complex.exists_root ( show Polynomial.degree (binomialLift n g) > 0 from
        Polynomial.natDegree_pos_iff_degree_pos.mp (by grind) )
    by_cases hζ' : ζ ∈ lowerHalf b
    · exact ⟨ζ, hζ, hζ'⟩
    · set f' := polarShift ζ f
      have hf' : (binomialLift (n - 1) f').natDegree = n - 1 := by
        have hf' : (polarDeriv n ζ (binomialLift n f)).natDegree = n - 1 := by
          apply polarDeriv_natDegree_lowerHalf
          · grind
          · simp [*]
          · exact hroots
          · simp [*]
        rw [polarDeriv_binomialLift (Nat.pos_of_ne_zero hn) ζ f] at hf'
        rwa [Polynomial.natDegree_C_mul] at hf'
        simp_all
      have hf'_roots : (binomialLift (n - 1) f').RootsIn (lowerHalf b) := by
        have := polarDeriv_rootsIn_lowerHalf (Nat.pos_of_ne_zero hn) hf hroots hζ'
        have := polarDeriv_binomialLift (Nat.pos_of_ne_zero hn) ζ f
        simp_all [RootsIn]
        grind
      obtain ⟨g', hg'⟩ :
          ∃ g' : ℂ[X], (X - C ζ) * binomialLift (n - 1) g' = binomialLift n g := by
        obtain ⟨g', hg'⟩ : ∃ g' : ℂ[X], binomialLift n g = (X - C ζ) * g' := by
          exact Polynomial.dvd_iff_isRoot.mpr hζ
        have : g'.natDegree = n - 1 := by
          rw [hg', Polynomial.natDegree_mul'] at hg <;> aesop
        obtain ⟨_, _⟩ := exists_binomialLift_eq g' (by linarith)
        grind
      have hap' : AreApolar (n - 1) f' g' := by
        convert apolarPairing_deflation (Nat.pos_of_ne_zero hn) hg' using 1
        rw [hap]
        rfl
      obtain ⟨w, hw⟩ :
          ∃ w : ℂ, (binomialLift (n - 1) g').IsRoot w ∧ w ∈ lowerHalf b := by
        apply ih (n - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hn) (by simp [*]))
          f' g' hf' (by
            replace hg' := congr_arg Polynomial.natDegree hg'
            rw [Polynomial.natDegree_mul'] at hg' <;> norm_num at *
            · lia
            · intro H
              simp_all +decide) hap' hf'_roots
      exact ⟨w, by replace hg' := congr_arg (Polynomial.eval w) hg'; simp_all⟩

theorem grace_apolarity_lowerHalf {n : Nat} {b : ℝ} {f g : ℂ[X]}
    (hf : (binomialLift n f).natDegree = n) (hg : (binomialLift n g).natDegree = n)
    (hap : AreApolar n f g)
    (hroots : (binomialLift n f).RootsIn (lowerHalf b)) :
    (binomialLift n g).HasRootIn (lowerHalf b) :=
  grace_aux_lowerHalf n f g hf hg hap hroots

def upperHalf (b : ℝ) : Set ℂ := {z : ℂ | b ≤ z.im}

@[simp] theorem mem_upperHalf {b : ℝ} {z : ℂ} : z ∈ upperHalf b ↔ b ≤ z.im := Iff.rfl

noncomputable def negComp (p : ℂ[X]) : ℂ[X] := p.comp (-X)

@[simp] theorem coeff_negComp (p : ℂ[X]) (k : ℕ) :
    (negComp p).coeff k = (-1) ^ k * p.coeff k := by
  have hpow : ∀ i : ℕ, (-X : ℂ[X]) ^ i = C ((-1) ^ i) * X ^ i := by
    intro i
    rw [show (-X : ℂ[X]) = C (-1) * X by simp, mul_pow, ← C_pow]
  simp only [negComp, Polynomial.comp, Polynomial.eval₂_eq_sum, Polynomial.sum_def, hpow,
    ← mul_assoc]
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · simp only [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp [mul_comm]
  · intro i _ hik
    simp only [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp [Ne.symm hik]
  · simp_all

theorem negComp_binomialLift (n : Nat) (p : ℂ[X]) :
    binomialLift n (negComp p) = negComp (binomialLift n p) := by
  ext k
  rw [coeff_binomialLift, coeff_negComp, coeff_negComp, coeff_binomialLift]
  grind

theorem areApolar_negComp_iff (n : Nat) (f g : ℂ[X]) :
    AreApolar n (negComp f) (negComp g) ↔ AreApolar n f g := by
  have : apolarPairing n (negComp f) (negComp g)
      = (-1) ^ n * apolarPairing n f g := by
    simp only [apolarPairing, coeff_negComp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp [*]
    have : (-1 : ℂ) ^ (n - k) = (-1) ^ n * (-1) ^ k := by
      have : (-1 : ℂ) ^ n = (-1) ^ (n - k) * (-1) ^ k := by rw [← pow_add, Nat.sub_add_cancel hkn]
      grind
    grind
  unfold AreApolar
  simp [*]

theorem grace_apolarity_upperHalf {n : Nat} {b : ℝ} {f g : ℂ[X]}
    (hf : (binomialLift n f).natDegree = n) (hg : (binomialLift n g).natDegree = n)
    (hap : AreApolar n f g)
    (hroots : (binomialLift n f).RootsIn (upperHalf b)) :
    (binomialLift n g).HasRootIn (upperHalf b) := by
  have hfhat : (binomialLift n (negComp f)).natDegree = n := by
    rw [negComp_binomialLift, negComp, Polynomial.natDegree_comp]
    simp [*]
  have hghat : (binomialLift n (negComp g)).natDegree = n := by
    rw [negComp_binomialLift, negComp, Polynomial.natDegree_comp]
    simp [*]
  have haphat : AreApolar n (negComp f) (negComp g) :=
    (areApolar_negComp_iff n f g).mpr hap
  have hroothat : (binomialLift n (negComp f)).RootsIn (lowerHalf (-b)) := by
    rw [negComp_binomialLift]
    intro w hw
    have hAw : (binomialLift n f).IsRoot (-w) := by
      have := hw
      simp only [Polynomial.IsRoot, negComp, Polynomial.eval_comp, Polynomial.eval_neg,
        Polynomial.eval_X] at this
      simp [*]
    have hru := hroots (-w) hAw
    simp only [mem_upperHalf, Complex.neg_im] at hru
    simp only [mem_lowerHalf]
    linarith
  obtain ⟨w, hwroot, hwmem⟩ :=
    grace_apolarity_lowerHalf hfhat hghat haphat hroothat
  refine ⟨-w, ?_, ?_⟩
  · rw [negComp_binomialLift] at hwroot
    simp only [Polynomial.IsRoot, negComp, Polynomial.eval_comp, Polynomial.eval_neg,
      Polynomial.eval_X] at hwroot
    simp [*]
  · simp only [mem_lowerHalf] at hwmem
    simp only [mem_upperHalf, Complex.neg_im]
    linarith

end RealRooted
