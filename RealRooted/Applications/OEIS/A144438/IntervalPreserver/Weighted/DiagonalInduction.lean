import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.DirectResidueAlgebra
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.WeightedResidueSum

/-!
# Weighted diagonal induction for the A144438 interval transform

This file packages the simultaneous induction on splitting, simplicity,
negative root location, positive companion residues, and scaled residue
energy.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The five properties propagated together in the weighted diagonal proof. -/
structure WeightedDecoDiagonalInvariant (w a : ℝ) (n : ℕ) : Prop where
  splits : (weightedDecoDiagonal w n a).Splits
  simple : HasSimpleRoots (weightedDecoDiagonal w n a)
  roots_neg : ∀ r, (weightedDecoDiagonal w n a).IsRoot r → r < 0
  companion_residue_pos : ∀ r, (weightedDecoDiagonal w n a).IsRoot r →
    0 < (weightedDecoDiagonalCompanion w n a).eval r /
      (weightedDecoDiagonal w n a).derivative.eval r
  scaled_energy_le_one :
    weightedDecoScaledEnergy w (weightedDecoDiagonal w n a)
      (weightedDecoDiagonalCompanion w n a)
      (weightedDecoDiagonalLag w n a) ≤ 1

/-- The simultaneous invariant starts at degree one. -/
theorem weightedDecoDiagonalInvariant_one {w a : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ha0 : 0 ≤ a) :
    WeightedDecoDiagonalInvariant w a 1 := by
  have hp : weightedDecoDiagonal w 1 a = X + C (1 + a) :=
    weightedDecoDiagonal_one w a
  have hne : weightedDecoDiagonal w 1 a ≠ 0 :=
    (weightedDecoDiagonal_monic w 1 a).ne_zero
  refine ⟨?_, hasSimpleRoots_of_natDegree_le_one hne ?_, ?_, ?_,
    weightedDecoScaledEnergy_base_le_one hw0 hw1 ha0⟩
  · rw [hp]
    exact Polynomial.Splits.X_add_C (1 + a)
  · rw [weightedDecoDiagonal_natDegree]
  · intro r hr
    rw [hp] at hr
    simp only [Polynomial.IsRoot.def, eval_add, eval_X, eval_C] at hr
    linarith
  · intro r _hr
    rw [weightedDecoDiagonalCompanion_one, hp]
    simp
    linarith

-- The proof elaborates several nested finite subtype sums and rational identities.
/-- The residue-energy part of one weighted diagonal step. -/
theorem weightedDecoDiagonal_successor_residue_and_energy
    {w a : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (hinv : WeightedDecoDiagonalInvariant w a n) :
    (∀ r, (weightedDecoDiagonal w (n + 1) a).IsRoot r →
      0 < (weightedDecoDiagonalCompanion w (n + 1) a).eval r /
        (weightedDecoDiagonal w (n + 1) a).derivative.eval r) ∧
      weightedDecoScaledEnergy w (weightedDecoDiagonal w (n + 1) a)
        (weightedDecoDiagonalCompanion w (n + 1) a)
        (weightedDecoDiagonalLag w (n + 1) a) ≤ 1 := by
  classical
  let p := weightedDecoDiagonal w n a
  let h := weightedDecoDiagonalCompanion w n a
  let k := weightedDecoDiagonalLag w n a
  let q := weightedDecoDiagonal w (n + 1) a
  let hplus := weightedDecoDiagonalCompanion w (n + 1) a
  let kplus := weightedDecoDiagonalLag w (n + 1) a
  let r : ↑p.roots.toFinset → ℝ := fun i ↦ i.1
  let ω : ↑p.roots.toFinset → ℝ := fun i ↦
    h.eval (r i) / p.derivative.eval (r i)
  let t : ↑p.roots.toFinset → ℝ := fun i ↦
    k.eval (r i) / p.derivative.eval (r i)
  let V : ↑p.roots.toFinset → ℝ := fun i ↦ (-r i) * ω i
  let J : ↑p.roots.toFinset → ℝ := fun i ↦ (1 - r i) * V i
  let c : ↑p.roots.toFinset → ℝ := fun i ↦ -V i + w * a / 2 * t i
  let β : ℝ := 2 + w + (∑ i, ω i) - (n : ℝ) * a
  let κ := weightedDecoKappa w n a
  let η := weightedDecoEta w n a
  let H := weightedDecoScaledEnergy w p h k
  let s₀ : ℝ :=
    2 + w + (n : ℝ) * (1 - a) - η + w * (1 + a) * κ
  let S : ℝ := s₀ - w * a ^ 2 * H / 4
  have hnodup : p.roots.Nodup := hinv.simple.roots_nodup
  have hrneg : ∀ i, r i < 0 := by
    intro i
    exact hinv.roots_neg (r i)
      (isRoot_of_mem_roots (Multiset.mem_toFinset.mp i.2))
  have hωpos : ∀ i, 0 < ω i := by
    intro i
    exact hinv.companion_residue_pos (r i)
      (isRoot_of_mem_roots (Multiset.mem_toFinset.mp i.2))
  have hVpos : ∀ i, 0 < V i := by
    intro i
    exact mul_pos (neg_pos.mpr (hrneg i)) (hωpos i)
  have hJpos : ∀ i, 0 < J i := by
    intro i
    exact mul_pos (by linarith [hrneg i]) (hVpos i)
  have hH0 : 0 ≤ H := by
    dsimp only [H, weightedDecoScaledEnergy]
    exact mul_nonneg hw0 (a144438ResidueEnergy_nonneg
      (fun x hx ↦ hinv.companion_residue_pos x (isRoot_of_mem_roots hx))
      (fun x hx ↦ hinv.roots_neg x (isRoot_of_mem_roots hx)))
  have hH1 : H ≤ 1 := hinv.scaled_energy_le_one
  have hκBounds := weightedDeco_endpoint_bounds hw0 ha0 ha1 n hn
  have hκ0 : 0 ≤ κ := hκBounds.2.2.1
  have hκ1 : κ ≤ 1 / 2 := hκBounds.2.2.2
  have hηlt : η < 1 := weightedDecoEta_lt_one hw0 hn ha0 ha1
  have hcompanion : ∑ i, ω i / (1 - r i) =
      (n : ℝ) - η + w * κ := by
    dsimp only [r, ω]
    calc
      (∑ i : ↑p.roots.toFinset,
          h.eval i.1 / p.derivative.eval i.1 / (1 - i.1)) =
          ∑ x ∈ p.roots.toFinset,
            h.eval x / p.derivative.eval x / (1 - x) :=
        (Finset.sum_subtype p.roots.toFinset (fun _ ↦ Iff.rfl)
          (fun x ↦ h.eval x / p.derivative.eval x / (1 - x))).symm
      _ = (n : ℝ) - η + w * κ := by
        simpa only [p, h, η, κ] using
          weightedDecoDiagonalCompanion_residue_sum_eq hw0 hn ha0
            hinv.splits hnodup
  have hlag : ∑ i, t i / (1 - r i) = κ := by
    dsimp only [r, t]
    calc
      (∑ i : ↑p.roots.toFinset,
          k.eval i.1 / p.derivative.eval i.1 / (1 - i.1)) =
          ∑ x ∈ p.roots.toFinset,
            k.eval x / p.derivative.eval x / (1 - x) :=
        (Finset.sum_subtype p.roots.toFinset (fun _ ↦ Iff.rfl)
          (fun x ↦ k.eval x / p.derivative.eval x / (1 - x))).symm
      _ = κ := by
        simpa only [p, k, κ] using
          weightedDecoDiagonalLag_residue_sum_eq_kappa hw0 hn ha0
            hinv.splits hnodup
  have henergy : ∑ i, t i ^ 2 / ((1 - r i) * V i) =
      a144438ResidueEnergy p h k := by
    rw [weightedDeco_direct_energy_eq r ω t V (fun _ ↦ rfl)]
    dsimp only [r, ω, t]
    calc
      (∑ i : ↑p.roots.toFinset,
          (k.eval i.1 / p.derivative.eval i.1) ^ 2 /
            ((h.eval i.1 / p.derivative.eval i.1) * (-i.1) * (1 - i.1))) =
          ∑ x ∈ p.roots.toFinset,
            (k.eval x / p.derivative.eval x) ^ 2 /
              ((h.eval x / p.derivative.eval x) * (-x) * (1 - x)) :=
        (Finset.sum_subtype p.roots.toFinset (fun _ ↦ Iff.rfl)
          (fun x ↦ (k.eval x / p.derivative.eval x) ^ 2 /
            ((h.eval x / p.derivative.eval x) * (-x) * (1 - x)))).symm
      _ = a144438ResidueEnergy p h k := rfl
  have hscaled : w * a144438ResidueEnergy p h k = H := rfl
  have hschurEq : β - ∑ i, c i ^ 2 / J i = S := by
    dsimp only [β, c, J, S, s₀]
    simpa only [V, one_mul] using weightedDeco_direct_schur_eq
      r ω t V a w (n : ℝ) η κ (a144438ResidueEnergy p h k) H
      hrneg (fun _ ↦ rfl) (fun i ↦ (hVpos i).ne') hcompanion hlag
      henergy hscaled
  have hSpos : 0 < S := by
    dsimp only [S, s₀]
    exact weightedDeco_schur_pos ha0 ha1 hw0 hw1 hκ0 hηlt hH0 hH1
      (Nat.cast_nonneg n)
  have hs₀Lower : 1 + w + w * (1 + a) * κ < s₀ := by
    dsimp only [s₀]
    have hnTerm : 0 ≤ (n : ℝ) * (1 - a) := by positivity
    linarith
  let Φ : ℝ :=
    a ^ 2 * H + w * (1 + a * κ - a ^ 2 * H / 2) ^ 2 / S
  have hΦlt : Φ < 1 + a := by
    dsimp only [Φ, S]
    exact weightedDeco_residue_energy_scalar_lt ha0 ha1 hw0 hw1 hκ0 hκ1
      hH1 hs₀Lower
  have hblockNorm :
      w * (a ^ 2 * (∑ i, t i ^ 2 / J i) +
        (1 - a * (∑ i, t i * c i / J i)) ^ 2 / S) = Φ := by
    dsimp only [J, c, Φ]
    exact weightedDeco_direct_block_norm_eq r t V a w κ
      (a144438ResidueEnergy p h k) H S hrneg
      (fun i ↦ (hVpos i).ne') hlag henergy hscaled
  have hrootPackage := weightedDecoDiagonal_root_step hn ha0 hinv.splits
    hinv.companion_residue_pos hinv.roots_neg
  have hqrec : q = (1 + X + C a) * p + X * h :=
    weightedDecoDiagonal_succ w n a
  have hkplusRec : kplus = p + C a * k :=
    weightedDecoDiagonalLag_succ w n a
  have hhplusRec : hplus =
      (1 - X) * q.derivative + C ((n : ℝ) + 1) * q -
        C (((n : ℝ) + 1) * a) * p + C w * kplus := by
    exact weightedDecoDiagonalCompanion_succ_eq w n a
  have hrootwise : ∀ ρ, q.IsRoot ρ →
      0 < hplus.eval ρ / q.derivative.eval ρ ∧
        w * (kplus.eval ρ / q.derivative.eval ρ) ^ 2 /
            (hplus.eval ρ / q.derivative.eval ρ) ≤
          Φ * (p.eval ρ / q.derivative.eval ρ) := by
    intro ρ hqρ
    have hpρ : p.eval ρ ≠ 0 := by
      intro hpzero
      have hpRoot : p.IsRoot ρ := hpzero
      exact hrootPackage.2.2.2 ρ hpRoot hqρ
    have hρdiff : ∀ i, ρ - r i ≠ 0 := by
      intro i hzero
      have heq : ρ = r i := sub_eq_zero.mp hzero
      apply hpρ
      rw [heq]
      exact isRoot_of_mem_roots (Multiset.mem_toFinset.mp i.2)
    let y : ↑p.roots.toFinset → ℝ := fun i ↦ 1 / (ρ - r i)
    let D : ℝ := 1 + ∑ i, V i / (ρ - r i) ^ 2
    let L : ℝ := a * ∑ i, t i / (ρ - r i) + 1
    let A : ℝ :=
      (∑ i, J i * y i ^ 2) + 2 * (∑ i, c i * y i) + β
    have hDpos : 0 < D := by
      dsimp only [D]
      have hsum : 0 ≤ ∑ i, V i / (ρ - r i) ^ 2 := by
        exact Finset.sum_nonneg fun i _ ↦
          div_nonneg (hVpos i).le (sq_nonneg _)
      linarith
    have hhPartial : h.eval ρ / p.eval ρ =
        ∑ i, ω i / (ρ - r i) := by
      have hpartial := a144438_sum_companion_residue_div hinv.splits hnodup
        (by simpa only [p, weightedDecoDiagonal_natDegree] using hn)
        (by
          simpa only [p, h, weightedDecoDiagonal_natDegree] using
            weightedDecoDiagonalCompanion_degree_lt w hn a)
        hpρ
      dsimp only [r, ω]
      calc
        h.eval ρ / p.eval ρ =
            ∑ x ∈ p.roots.toFinset,
              (h.eval x / p.derivative.eval x) / (ρ - x) := hpartial
        _ = ∑ i : ↑p.roots.toFinset,
              (h.eval i.1 / p.derivative.eval i.1) / (ρ - i.1) :=
          Finset.sum_subtype p.roots.toFinset (fun _ ↦ Iff.rfl) _
    have hrootEq : 1 + ρ + a + ρ * ∑ i, ω i / (ρ - r i) = 0 := by
      have hqEval : (1 + ρ + a) * p.eval ρ + ρ * h.eval ρ = 0 := by
        rw [hqrec] at hqρ
        simpa [Polynomial.IsRoot.def] using hqρ
      have hhEval : h.eval ρ =
          p.eval ρ * (∑ i, ω i / (ρ - r i)) := by
        simpa only [mul_comm] using (div_eq_iff hpρ).mp hhPartial
      rw [hhEval] at hqEval
      have hfactor :
          (1 + ρ + a + ρ * ∑ i, ω i / (ρ - r i)) *
              p.eval ρ = 0 := by
        nlinarith
      exact (mul_eq_zero.mp hfactor).resolve_right hpρ
    have hmass : ∑ i, V i / (ρ - r i) =
        (∑ i, ω i) + 1 + ρ + a :=
      weightedDeco_direct_mass_eq r ω V a ρ hρdiff (fun _ ↦ rfl)
        hrootEq
    have hAeq : A = (1 - ρ) * D + w * L - ((n : ℝ) + 1) * a := by
      have hraw := weightedDeco_direct_successor_block_eq
        r ω t V a w (n : ℝ) ρ hρdiff hmass
      dsimp only [A, D, L, J, c, y, β]
      rw [show 1 + a * (∑ i, t i / (ρ - r i)) =
        a * (∑ i, t i / (ρ - r i)) + 1 by ring] at hraw
      exact hraw
    have hderivative : q.derivative.eval ρ = p.eval ρ * D := by
      have hformula := a144438_insertion_derivative_at_root hinv.splits hnodup
        (by simpa only [p, weightedDecoDiagonal_natDegree] using hn)
        (by
          simpa only [p, h, weightedDecoDiagonal_natDegree] using
            weightedDecoDiagonalCompanion_degree_lt w hn a)
        (hqrec ▸ hqρ) hpρ
      rw [hqrec]
      rw [hformula]
      congr 1
      dsimp only [D, V, r, ω]
      apply congrArg (fun z : ℝ ↦ 1 + z)
      rw [← Finset.sum_subtype p.roots.toFinset (fun _ ↦ Iff.rfl)
        (fun x ↦ (-x) * (h.eval x / p.derivative.eval x) / (ρ - x) ^ 2)]
    have hkplusEval : kplus.eval ρ = p.eval ρ * L := by
      rw [hkplusRec]
      have hformula := weightedDeco_insertion_lag_at_root
        (a := a) (ρ := ρ) hinv.splits hnodup
        (by simpa only [p, weightedDecoDiagonal_natDegree] using hn)
        (by
          simpa only [p, k, weightedDecoDiagonal_natDegree] using
            weightedDecoDiagonalLag_degree_lt w hn a)
        hpρ
      rw [hformula]
      congr 1
      dsimp only [L, r, t]
      rw [← Finset.sum_subtype p.roots.toFinset (fun _ ↦ Iff.rfl)
        (fun x ↦ (k.eval x / p.derivative.eval x) / (ρ - x))]
      ring
    have hhplusEval : hplus.eval ρ = p.eval ρ * A := by
      exact weightedDeco_insertion_companion_at_root hqρ hderivative
        hkplusEval hhplusRec hAeq
    have hblock := weightedDeco_rootwise_block_bound J c t y a β w D hJpos
      (by rwa [hschurEq]) hw0 hDpos
    have hApos : 0 < A := hblock.1
    have hratios := weightedDeco_insertion_residue_ratios hpρ hDpos.ne'
      hderivative hkplusEval hhplusEval
    constructor
    · rw [hratios.2.2]
      exact div_pos hApos hDpos
    · rw [hratios.1, hratios.2.1, hratios.2.2]
      have hblockNorm' :
          w * (a ^ 2 * (∑ i, t i ^ 2 / J i) +
            (1 - a * (∑ i, t i * c i / J i)) ^ 2 /
              (β - ∑ i, c i ^ 2 / J i)) = Φ := by
        rwa [hschurEq]
      calc
        w * (L / D) ^ 2 / (A / D) ≤
            w * (a ^ 2 * (∑ i, t i ^ 2 / J i) +
              (1 - a * (∑ i, t i * c i / J i)) ^ 2 /
                (β - ∑ i, c i ^ 2 / J i)) / D := by
          have hblockBound := hblock.2
          dsimp only [y] at hblockBound
          dsimp only [L, A, y]
          simpa only [div_eq_mul_inv, one_mul] using hblockBound
        _ = Φ / D := by rw [hblockNorm']
        _ = Φ * (1 / D) := by ring
  constructor
  · intro ρ hqρ
    exact (hrootwise ρ hqρ).1
  · have hqSplits : q.Splits := hrootPackage.1.2.1.2
    have hqSimple : HasSimpleRoots q := hrootPackage.2.1
    have hqNodup : q.roots.Nodup := hqSimple.roots_nodup
    have hqNeg : ∀ ρ, q.IsRoot ρ → ρ < 0 := hrootPackage.2.2.1
    have hsumBound :
        ∑ ρ ∈ q.roots.toFinset,
            w * (kplus.eval ρ / q.derivative.eval ρ) ^ 2 /
              ((hplus.eval ρ / q.derivative.eval ρ) * (-ρ) * (1 - ρ)) ≤
          Φ * ∑ ρ ∈ q.roots.toFinset,
            (p.eval ρ / q.derivative.eval ρ) / ((-ρ) * (1 - ρ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ρ hρmem
      have hqρ : q.IsRoot ρ :=
        isRoot_of_mem_roots (Multiset.mem_toFinset.mp hρmem)
      have hlocal := hrootwise ρ hqρ
      have hρneg := hqNeg ρ hqρ
      have hweight : 0 < (-ρ) * (1 - ρ) :=
        mul_pos (neg_pos.mpr hρneg) (by linarith)
      have hdiv := div_le_div_of_nonneg_right hlocal.2 hweight.le
      calc
        w * (kplus.eval ρ / q.derivative.eval ρ) ^ 2 /
              ((hplus.eval ρ / q.derivative.eval ρ) * (-ρ) * (1 - ρ)) =
            (w * (kplus.eval ρ / q.derivative.eval ρ) ^ 2 /
              (hplus.eval ρ / q.derivative.eval ρ)) /
                ((-ρ) * (1 - ρ)) := by
          field_simp [hlocal.1.ne', hweight.ne']
        _ ≤ (Φ * (p.eval ρ / q.derivative.eval ρ)) /
              ((-ρ) * (1 - ρ)) := hdiv
        _ = Φ * ((p.eval ρ / q.derivative.eval ρ) /
              ((-ρ) * (1 - ρ))) := by ring
    have hq0 : q.eval 0 ≠ 0 := by
      dsimp only [q]
      rw [weightedDecoDiagonal_eval_zero]
      positivity
    have hq1 : q.eval 1 ≠ 0 :=
      (weightedDecoDiagonal_eval_one_pos hw0 ha0).ne'
    have hpDegree : p.degree < q.natDegree := by
      dsimp only [q]
      rw [weightedDecoDiagonal_natDegree]
      have hpne : p ≠ 0 :=
        (weightedDecoDiagonal_monic w n a).ne_zero
      rw [Polynomial.degree_eq_natDegree hpne]
      dsimp only [p]
      rw [weightedDecoDiagonal_natDegree]
      exact_mod_cast Nat.lt_succ_self n
    have hmassRaw := a144438_weighted_residue_sum_sub_eval hqSplits hqNodup
      (by dsimp only [q]; rw [weightedDecoDiagonal_natDegree]; lia)
      hpDegree hq0 hq1
    have hzeroRatio : p.eval 0 / q.eval 0 = 1 / (1 + a) := by
      dsimp only [p, q]
      rw [weightedDecoDiagonal_eval_zero, weightedDecoDiagonal_eval_zero,
        pow_succ]
      have hbase : 1 + a ≠ 0 := (by linarith : 0 < 1 + a).ne'
      have hpow : (1 + a) ^ n ≠ 0 := pow_ne_zero _ hbase
      field_simp [hbase, hpow]
    have honeRatio :
        p.eval 1 / q.eval 1 = 1 / weightedDecoEndpointRatio w (n + 1) a := by
      have hp1 : 0 < p.eval 1 := weightedDecoDiagonal_eval_one_pos hw0 ha0
      have hq1pos : 0 < q.eval 1 := weightedDecoDiagonal_eval_one_pos hw0 ha0
      rw [weightedDecoEndpointRatio, show n + 1 - 1 = n by lia]
      dsimp only [weightedDecoDiagonalAtOne, p, q]
      field_simp [hp1.ne', hq1pos.ne']
    have hmass :
        ∑ ρ ∈ q.roots.toFinset,
            (p.eval ρ / q.derivative.eval ρ) / ((-ρ) * (1 - ρ)) =
          1 / (1 + a) - 1 / weightedDecoEndpointRatio w (n + 1) a := by
      rw [hmassRaw, hzeroRatio, honeRatio]
    have hgammaFloor :=
      (weightedDeco_endpoint_bounds hw0 ha0 ha1 (n + 1) (by lia)).2.1
    have hgammaPos : 0 < weightedDecoEndpointRatio w (n + 1) a := by
      linarith
    have hbasePos : 0 < 1 + a := by linarith
    have hmassPos :
        0 < 1 / (1 + a) - 1 / weightedDecoEndpointRatio w (n + 1) a := by
      rw [sub_pos, div_lt_div_iff₀ hgammaPos hbasePos]
      linarith
    have hmassLt :
        1 / (1 + a) - 1 / weightedDecoEndpointRatio w (n + 1) a <
          1 / (1 + a) := by
      have : 0 < 1 / weightedDecoEndpointRatio w (n + 1) a := by positivity
      linarith
    have hproduct :
        Φ * (1 / (1 + a) - 1 / weightedDecoEndpointRatio w (n + 1) a) < 1 := by
      calc
        Φ * (1 / (1 + a) - 1 / weightedDecoEndpointRatio w (n + 1) a) <
            (1 + a) *
              (1 / (1 + a) - 1 / weightedDecoEndpointRatio w (n + 1) a) :=
          mul_lt_mul_of_pos_right hΦlt hmassPos
        _ < (1 + a) * (1 / (1 + a)) :=
          mul_lt_mul_of_pos_left hmassLt hbasePos
        _ = 1 := by field_simp [hbasePos.ne']
    dsimp only [weightedDecoScaledEnergy]
    unfold a144438ResidueEnergy
    rw [Finset.mul_sum]
    calc
      ∑ x ∈ q.roots.toFinset,
          w * ((kplus.eval x / q.derivative.eval x) ^ 2 /
            ((hplus.eval x / q.derivative.eval x) * (-x) * (1 - x))) =
          ∑ x ∈ q.roots.toFinset,
            w * (kplus.eval x / q.derivative.eval x) ^ 2 /
              ((hplus.eval x / q.derivative.eval x) * (-x) * (1 - x)) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ Φ * ∑ ρ ∈ q.roots.toFinset,
          (p.eval ρ / q.derivative.eval ρ) / ((-ρ) * (1 - ρ)) :=
        hsumBound
      _ = Φ * (1 / (1 + a) - 1 / weightedDecoEndpointRatio w (n + 1) a) := by
        rw [hmass]
      _ ≤ 1 := hproduct.le

/-- One recurrence step preserves the simultaneous diagonal invariant. -/
theorem WeightedDecoDiagonalInvariant.succ
    {w a : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (hinv : WeightedDecoDiagonalInvariant w a n) :
    WeightedDecoDiagonalInvariant w a (n + 1) := by
  have hroot := weightedDecoDiagonal_root_step hn ha0 hinv.splits
    hinv.companion_residue_pos hinv.roots_neg
  have hresidueEnergy := weightedDecoDiagonal_successor_residue_and_energy
    hw0 hw1 ha0 ha1 hn hinv
  exact ⟨hroot.1.2.1.2, hroot.2.1, hroot.2.2.1,
    hresidueEnergy.1, hresidueEnergy.2⟩

/-- The simultaneous weighted diagonal invariant holds in every positive
degree. -/
theorem weightedDecoDiagonalInvariant_all {w a : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ n : ℕ, 1 ≤ n → WeightedDecoDiagonalInvariant w a n := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => simpa using weightedDecoDiagonalInvariant_one hw0 hw1 ha0
  | succ m ih =>
      exact WeightedDecoDiagonalInvariant.succ hw0 hw1 ha0 ha1 (by lia)
        (ih (by lia))

/-- Every positive-rank weighted diagonal polynomial has simple negative
zeros throughout the full parameter square. -/
theorem weightedDecoDiagonal_hasSimpleRoots_and_roots_neg
    {w a : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    HasSimpleRoots (weightedDecoDiagonal w n a) ∧
      ∀ r, (weightedDecoDiagonal w n a).IsRoot r → r < 0 := by
  have hinv := weightedDecoDiagonalInvariant_all hw0 hw1 ha0 ha1 n hn
  exact ⟨hinv.simple, hinv.roots_neg⟩

/-- Consecutive positive-rank weighted diagonal polynomials strictly
interlace. -/
theorem weightedDecoDiagonal_strictInterl_succ
    {w a : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    StrictInterl (weightedDecoDiagonal w n a)
      (weightedDecoDiagonal w (n + 1) a) := by
  have hinv := weightedDecoDiagonalInvariant_all hw0 hw1 ha0 ha1 n hn
  exact (weightedDecoDiagonal_root_step hn ha0 hinv.splits
    hinv.companion_residue_pos hinv.roots_neg).1

end RealRooted.Applications.OEIS
